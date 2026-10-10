import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23296 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23296 raw23296Labels = mixedMoment B node1381 node1381Labels := by
  calc
    mixedMoment B raw23296 raw23296Labels = mixedMoment B raw23296step0 raw23296step0Labels := by
      have ha : raw23296step0 = (fun i j => raw23296 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23296step0 raw23296; decide +kernel
      have hl : raw23296step0Labels = raw23296Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23296 raw23296Labels permutation152 permutation7
    mixedMoment B raw23296step0 raw23296step0Labels = mixedMoment B raw23296step1 raw23296step1Labels := by
      have ha : raw23296step1 = raw23296step0 := by apply Matrix.ext; unfold raw23296step1 raw23296step0; decide +kernel
      have hl : raw23296step0Labels = labelEmbedding1 ∘ raw23296step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23296step0 raw23296step0Labels raw23296step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1381 node1381Labels := by rfl

def raw23297 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23297step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23297 raw23297Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw23297 raw23297Labels = mixedMoment B raw23297step0 raw23297step0Labels := by
      have hz : ∀ j, raw23297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23297step0 = (fun i j => raw23297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23297step0 raw23297; decide +kernel
      have hl : raw23297step0Labels = raw23297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23297 raw23297Labels permutation434 hz
    mixedMoment B raw23297step0 raw23297step0Labels = mixedMoment B raw23297step1 raw23297step1Labels := by
      have ha : raw23297step1 = (fun i j => raw23297step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23297step1 raw23297step0; decide +kernel
      have hl : raw23297step1Labels = raw23297step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23297step0 raw23297step0Labels permutation33 permutation7
    mixedMoment B raw23297step1 raw23297step1Labels = mixedMoment B raw23297step2 raw23297step2Labels := by
      have ha : raw23297step2 = raw23297step1 := by apply Matrix.ext; unfold raw23297step2 raw23297step1; decide +kernel
      have hl : raw23297step1Labels = labelEmbedding1 ∘ raw23297step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23297step1 raw23297step1Labels raw23297step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1391 node1391Labels := by rfl

def raw23298 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23298step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23298 raw23298Labels = mixedMoment B node1479 node1479Labels := by
  calc
    mixedMoment B raw23298 raw23298Labels = mixedMoment B raw23298step0 raw23298step0Labels := by
      have hz : ∀ j, raw23298 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23298step0 = (fun i j => raw23298 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23298step0 raw23298; decide +kernel
      have hl : raw23298step0Labels = raw23298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23298 raw23298Labels permutation346 hz
    mixedMoment B raw23298step0 raw23298step0Labels = mixedMoment B raw23298step1 raw23298step1Labels := by
      have ha : raw23298step1 = (fun i j => raw23298step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23298step1 raw23298step0; decide +kernel
      have hl : raw23298step1Labels = raw23298step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23298step0 raw23298step0Labels permutation32 permutation7
    mixedMoment B raw23298step1 raw23298step1Labels = mixedMoment B raw23298step2 raw23298step2Labels := by
      have ha : raw23298step2 = raw23298step1 := by apply Matrix.ext; unfold raw23298step2 raw23298step1; decide +kernel
      have hl : raw23298step1Labels = labelEmbedding1 ∘ raw23298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23298step1 raw23298step1Labels raw23298step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1479 node1479Labels := by rfl

def raw23299 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23299step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23299step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23299step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23299step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23299step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23299 raw23299Labels = mixedMoment B node1420 node1420Labels := by
  calc
    mixedMoment B raw23299 raw23299Labels = mixedMoment B raw23299step0 raw23299step0Labels := by
      have hz : ∀ j, raw23299 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23299step0 = (fun i j => raw23299 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23299step0 raw23299; decide +kernel
      have hl : raw23299step0Labels = raw23299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23299 raw23299Labels permutation346 hz
    mixedMoment B raw23299step0 raw23299step0Labels = mixedMoment B raw23299step1 raw23299step1Labels := by
      have hz : ∀ j, raw23299step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23299step1 = (fun i j => raw23299step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23299step1 raw23299step0; decide +kernel
      have hl : raw23299step1Labels = raw23299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23299step0 raw23299step0Labels permutation56 hz
    mixedMoment B raw23299step1 raw23299step1Labels = mixedMoment B raw23299step2 raw23299step2Labels := by
      have ha : raw23299step2 = (fun i j => raw23299step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23299step2 raw23299step1; decide +kernel
      have hl : raw23299step2Labels = raw23299step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23299step1 raw23299step1Labels permutation8 permutation7
    mixedMoment B raw23299step2 raw23299step2Labels = mixedMoment B raw23299step3 raw23299step3Labels := by
      have ha : raw23299step3 = raw23299step2 := by apply Matrix.ext; unfold raw23299step3 raw23299step2; decide +kernel
      have hl : raw23299step2Labels = labelEmbedding1 ∘ raw23299step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23299step2 raw23299step2Labels raw23299step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1420 node1420Labels := by rfl

def raw23300 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23300 raw23300Labels = mixedMoment B node1381 node1381Labels := by
  calc
    mixedMoment B raw23300 raw23300Labels = mixedMoment B raw23300step0 raw23300step0Labels := by
      have ha : raw23300step0 = (fun i j => raw23300 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23300step0 raw23300; decide +kernel
      have hl : raw23300step0Labels = raw23300Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23300 raw23300Labels permutation158 permutation7
    mixedMoment B raw23300step0 raw23300step0Labels = mixedMoment B raw23300step1 raw23300step1Labels := by
      have ha : raw23300step1 = raw23300step0 := by apply Matrix.ext; unfold raw23300step1 raw23300step0; decide +kernel
      have hl : raw23300step0Labels = labelEmbedding1 ∘ raw23300step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23300step0 raw23300step0Labels raw23300step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1381 node1381Labels := by rfl

def raw23301 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw23301step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23301 raw23301Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw23301 raw23301Labels = mixedMoment B raw23301step0 raw23301step0Labels := by
      have hz : ∀ j, raw23301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23301step0 = (fun i j => raw23301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23301step0 raw23301; decide +kernel
      have hl : raw23301step0Labels = raw23301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23301 raw23301Labels permutation346 hz
    mixedMoment B raw23301step0 raw23301step0Labels = mixedMoment B raw23301step1 raw23301step1Labels := by
      have ha : raw23301step1 = (fun i j => raw23301step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23301step1 raw23301step0; decide +kernel
      have hl : raw23301step1Labels = raw23301step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23301step0 raw23301step0Labels permutation33 permutation7
    mixedMoment B raw23301step1 raw23301step1Labels = mixedMoment B raw23301step2 raw23301step2Labels := by
      have ha : raw23301step2 = raw23301step1 := by apply Matrix.ext; unfold raw23301step2 raw23301step1; decide +kernel
      have hl : raw23301step1Labels = labelEmbedding1 ∘ raw23301step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23301step1 raw23301step1Labels raw23301step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1391 node1391Labels := by rfl

def raw23302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23302step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23302step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23302step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23302 raw23302Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw23302 raw23302Labels = mixedMoment B raw23302step0 raw23302step0Labels := by
      have hz : ∀ j, raw23302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23302step0 = (fun i j => raw23302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23302step0 raw23302; decide +kernel
      have hl : raw23302step0Labels = raw23302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23302 raw23302Labels permutation434 hz
    mixedMoment B raw23302step0 raw23302step0Labels = mixedMoment B raw23302step1 raw23302step1Labels := by
      have hz : ∀ j, raw23302step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23302step1 = (fun i j => raw23302step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23302step1 raw23302step0; decide +kernel
      have hl : raw23302step1Labels = raw23302step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23302step0 raw23302step0Labels permutation80 hz
    mixedMoment B raw23302step1 raw23302step1Labels = mixedMoment B raw23302step2 raw23302step2Labels := by
      have ha : raw23302step2 = (fun i j => raw23302step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23302step2 raw23302step1; decide +kernel
      have hl : raw23302step2Labels = raw23302step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23302step1 raw23302step1Labels permutation8 permutation7
    mixedMoment B raw23302step2 raw23302step2Labels = mixedMoment B raw23302step3 raw23302step3Labels := by
      have ha : raw23302step3 = raw23302step2 := by apply Matrix.ext; unfold raw23302step3 raw23302step2; decide +kernel
      have hl : raw23302step2Labels = labelEmbedding1 ∘ raw23302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23302step2 raw23302step2Labels raw23302step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw23303 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23303step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23303step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23303step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23303step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23303step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23303step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23303 raw23303Labels = mixedMoment B node1486 node1486Labels := by
  calc
    mixedMoment B raw23303 raw23303Labels = mixedMoment B raw23303step0 raw23303step0Labels := by
      have hz : ∀ j, raw23303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23303step0 = (fun i j => raw23303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23303step0 raw23303; decide +kernel
      have hl : raw23303step0Labels = raw23303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23303 raw23303Labels permutation434 hz
    mixedMoment B raw23303step0 raw23303step0Labels = mixedMoment B raw23303step1 raw23303step1Labels := by
      have hz : ∀ j, raw23303step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23303step1 = (fun i j => raw23303step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23303step1 raw23303step0; decide +kernel
      have hl : raw23303step1Labels = raw23303step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23303step0 raw23303step0Labels permutation80 hz
    mixedMoment B raw23303step1 raw23303step1Labels = mixedMoment B raw23303step2 raw23303step2Labels := by
      have ha : raw23303step2 = (fun i j => raw23303step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23303step2 raw23303step1; decide +kernel
      have hl : raw23303step2Labels = raw23303step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23303step1 raw23303step1Labels permutation9 permutation7
    mixedMoment B raw23303step2 raw23303step2Labels = mixedMoment B raw23303step3 raw23303step3Labels := by
      have ha : raw23303step3 = raw23303step2 := by apply Matrix.ext; unfold raw23303step3 raw23303step2; decide +kernel
      have hl : raw23303step2Labels = labelEmbedding1 ∘ raw23303step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23303step2 raw23303step2Labels raw23303step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1486 node1486Labels := by rfl

def raw23304 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23304step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23304step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23304step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -1, 2], ![0, -2, 2]]
def raw23304step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23304step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23304step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23304step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23304step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23304 raw23304Labels = mixedMoment B node1455 node1455Labels := by
  calc
    mixedMoment B raw23304 raw23304Labels = mixedMoment B raw23304step0 raw23304step0Labels := by
      have hz : ∀ j, raw23304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23304step0 = (fun i j => raw23304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23304step0 raw23304; decide +kernel
      have hl : raw23304step0Labels = raw23304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23304 raw23304Labels permutation434 hz
    mixedMoment B raw23304step0 raw23304step0Labels = mixedMoment B raw23304step1 raw23304step1Labels := by
      have hz : ∀ j, raw23304step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23304step1 = (fun i j => raw23304step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23304step1 raw23304step0; decide +kernel
      have hl : raw23304step1Labels = raw23304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23304step0 raw23304step0Labels permutation80 hz
    mixedMoment B raw23304step1 raw23304step1Labels = mixedMoment B raw23304step2 raw23304step2Labels := by
      have hz : ∀ j, raw23304step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23304step2 = (fun i j => raw23304step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23304step2 raw23304step1; decide +kernel
      have hl : raw23304step2Labels = raw23304step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23304step1 raw23304step1Labels permutation14 hz
    mixedMoment B raw23304step2 raw23304step2Labels = mixedMoment B raw23304step3 raw23304step3Labels := by
      have ha : raw23304step3 = (fun i j => raw23304step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23304step3 raw23304step2; decide +kernel
      have hl : raw23304step3Labels = raw23304step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23304step2 raw23304step2Labels permutation3 permutation7
    mixedMoment B raw23304step3 raw23304step3Labels = mixedMoment B raw23304step4 raw23304step4Labels := by
      have ha : raw23304step4 = raw23304step3 := by apply Matrix.ext; unfold raw23304step4 raw23304step3; decide +kernel
      have hl : raw23304step3Labels = labelEmbedding1 ∘ raw23304step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23304step3 raw23304step3Labels raw23304step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1455 node1455Labels := by rfl

def raw23305 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23305step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23305step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23305 raw23305Labels = mixedMoment B node1401 node1401Labels := by
  calc
    mixedMoment B raw23305 raw23305Labels = mixedMoment B raw23305step0 raw23305step0Labels := by
      have hz : ∀ j, raw23305 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23305step0 = (fun i j => raw23305 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23305step0 raw23305; decide +kernel
      have hl : raw23305step0Labels = raw23305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23305 raw23305Labels permutation434 hz
    mixedMoment B raw23305step0 raw23305step0Labels = mixedMoment B raw23305step1 raw23305step1Labels := by
      have ha : raw23305step1 = (fun i j => raw23305step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23305step1 raw23305step0; decide +kernel
      have hl : raw23305step1Labels = raw23305step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23305step0 raw23305step0Labels permutation33 permutation7
    mixedMoment B raw23305step1 raw23305step1Labels = mixedMoment B raw23305step2 raw23305step2Labels := by
      have ha : raw23305step2 = raw23305step1 := by apply Matrix.ext; unfold raw23305step2 raw23305step1; decide +kernel
      have hl : raw23305step1Labels = labelEmbedding1 ∘ raw23305step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23305step1 raw23305step1Labels raw23305step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1401 node1401Labels := by rfl

def raw23306 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23306step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23306 raw23306Labels = mixedMoment B node1401 node1401Labels := by
  calc
    mixedMoment B raw23306 raw23306Labels = mixedMoment B raw23306step0 raw23306step0Labels := by
      have hz : ∀ j, raw23306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23306step0 = (fun i j => raw23306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23306step0 raw23306; decide +kernel
      have hl : raw23306step0Labels = raw23306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23306 raw23306Labels permutation346 hz
    mixedMoment B raw23306step0 raw23306step0Labels = mixedMoment B raw23306step1 raw23306step1Labels := by
      have ha : raw23306step1 = (fun i j => raw23306step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23306step1 raw23306step0; decide +kernel
      have hl : raw23306step1Labels = raw23306step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23306step0 raw23306step0Labels permutation33 permutation7
    mixedMoment B raw23306step1 raw23306step1Labels = mixedMoment B raw23306step2 raw23306step2Labels := by
      have ha : raw23306step2 = raw23306step1 := by apply Matrix.ext; unfold raw23306step2 raw23306step1; decide +kernel
      have hl : raw23306step1Labels = labelEmbedding1 ∘ raw23306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23306step1 raw23306step1Labels raw23306step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1401 node1401Labels := by rfl

def raw23307 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw23307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw23307step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw23307step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23307step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23307step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23307step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23307step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23307 raw23307Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw23307 raw23307Labels = mixedMoment B raw23307step0 raw23307step0Labels := by
      have hz : ∀ j, raw23307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23307step0 = (fun i j => raw23307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23307step0 raw23307; decide +kernel
      have hl : raw23307step0Labels = raw23307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23307 raw23307Labels permutation434 hz
    mixedMoment B raw23307step0 raw23307step0Labels = mixedMoment B raw23307step1 raw23307step1Labels := by
      have hz : ∀ j, raw23307step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23307step1 = (fun i j => raw23307step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23307step1 raw23307step0; decide +kernel
      have hl : raw23307step1Labels = raw23307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23307step0 raw23307step0Labels permutation80 hz
    mixedMoment B raw23307step1 raw23307step1Labels = mixedMoment B raw23307step2 raw23307step2Labels := by
      have ha : raw23307step2 = (fun i j => raw23307step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23307step2 raw23307step1; decide +kernel
      have hl : raw23307step2Labels = raw23307step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23307step1 raw23307step1Labels permutation9 permutation7
    mixedMoment B raw23307step2 raw23307step2Labels = mixedMoment B raw23307step3 raw23307step3Labels := by
      have ha : raw23307step3 = raw23307step2 := by apply Matrix.ext; unfold raw23307step3 raw23307step2; decide +kernel
      have hl : raw23307step2Labels = labelEmbedding1 ∘ raw23307step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23307step2 raw23307step2Labels raw23307step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw23308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23308 raw23308Labels = mixedMoment B node984 node984Labels := by
  calc
    mixedMoment B raw23308 raw23308Labels = mixedMoment B raw23308step0 raw23308step0Labels := by
      have hz : ∀ j, raw23308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23308step0 = (fun i j => raw23308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23308step0 raw23308; decide +kernel
      have hl : raw23308step0Labels = raw23308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23308 raw23308Labels permutation346 hz
    mixedMoment B raw23308step0 raw23308step0Labels = mixedMoment B raw23308step1 raw23308step1Labels := by
      have ha : raw23308step1 = (fun i j => raw23308step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23308step1 raw23308step0; decide +kernel
      have hl : raw23308step1Labels = raw23308step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23308step0 raw23308step0Labels permutation39 permutation2
    _ = mixedMoment B node984 node984Labels := by rfl

def raw23309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23309 raw23309Labels = mixedMoment B node2081 node2081Labels := by
  calc
    mixedMoment B raw23309 raw23309Labels = mixedMoment B raw23309step0 raw23309step0Labels := by
      have hz : ∀ j, raw23309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23309step0 = (fun i j => raw23309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23309step0 raw23309; decide +kernel
      have hl : raw23309step0Labels = raw23309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23309 raw23309Labels permutation346 hz
    mixedMoment B raw23309step0 raw23309step0Labels = mixedMoment B raw23309step1 raw23309step1Labels := by
      have ha : raw23309step1 = (fun i j => raw23309step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23309step1 raw23309step0; decide +kernel
      have hl : raw23309step1Labels = raw23309step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23309step0 raw23309step0Labels permutation33 permutation2
    _ = mixedMoment B node2081 node2081Labels := by rfl

def raw23310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23310 raw23310Labels = mixedMoment B node1989 node1989Labels := by
  calc
    mixedMoment B raw23310 raw23310Labels = mixedMoment B raw23310step0 raw23310step0Labels := by
      have ha : raw23310step0 = (fun i j => raw23310 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23310step0 raw23310; decide +kernel
      have hl : raw23310step0Labels = raw23310Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23310 raw23310Labels permutation183 permutation2
    _ = mixedMoment B node1989 node1989Labels := by rfl

def raw23311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw23311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23311 raw23311Labels = mixedMoment B node1917 node1917Labels := by
  calc
    mixedMoment B raw23311 raw23311Labels = mixedMoment B raw23311step0 raw23311step0Labels := by
      have hz : ∀ j, raw23311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23311step0 = (fun i j => raw23311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23311step0 raw23311; decide +kernel
      have hl : raw23311step0Labels = raw23311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23311 raw23311Labels permutation346 hz
    mixedMoment B raw23311step0 raw23311step0Labels = mixedMoment B raw23311step1 raw23311step1Labels := by
      have ha : raw23311step1 = (fun i j => raw23311step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23311step1 raw23311step0; decide +kernel
      have hl : raw23311step1Labels = raw23311step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23311step0 raw23311step0Labels permutation39 permutation2
    _ = mixedMoment B node1917 node1917Labels := by rfl

def raw23312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw23312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw23312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw23312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23312 raw23312Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw23312 raw23312Labels = mixedMoment B raw23312step0 raw23312step0Labels := by
      have hz : ∀ j, raw23312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23312step0 = (fun i j => raw23312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23312step0 raw23312; decide +kernel
      have hl : raw23312step0Labels = raw23312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23312 raw23312Labels permutation346 hz
    mixedMoment B raw23312step0 raw23312step0Labels = mixedMoment B raw23312step1 raw23312step1Labels := by
      have ha : raw23312step1 = (fun i j => raw23312step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23312step1 raw23312step0; decide +kernel
      have hl : raw23312step1Labels = raw23312step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23312step0 raw23312step0Labels permutation38 permutation2
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw23313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw23313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw23313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw23313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23313 raw23313Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw23313 raw23313Labels = mixedMoment B raw23313step0 raw23313step0Labels := by
      have hz : ∀ j, raw23313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23313step0 = (fun i j => raw23313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23313step0 raw23313; decide +kernel
      have hl : raw23313step0Labels = raw23313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23313 raw23313Labels permutation346 hz
    mixedMoment B raw23313step0 raw23313step0Labels = mixedMoment B raw23313step1 raw23313step1Labels := by
      have ha : raw23313step1 = (fun i j => raw23313step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23313step1 raw23313step0; decide +kernel
      have hl : raw23313step1Labels = raw23313step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23313step0 raw23313step0Labels permutation39 permutation2
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw23314 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![3, -3], ![0, 0]]
def raw23314Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23314step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![3, -3]]
def raw23314step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23314step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw23314step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23314step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw23314step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23314 raw23314Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw23314 raw23314Labels = mixedMoment B raw23314step0 raw23314step0Labels := by
      have hz : ∀ j, raw23314 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw23314step0 = (fun i j => raw23314 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw23314step0 raw23314; decide +kernel
      have hl : raw23314step0Labels = raw23314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23314 raw23314Labels permutation590 hz
    mixedMoment B raw23314step0 raw23314step0Labels = mixedMoment B raw23314step1 raw23314step1Labels := by
      have hz : ∀ j, raw23314step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23314step1 = (fun i j => raw23314step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23314step1 raw23314step0; decide +kernel
      have hl : raw23314step1Labels = raw23314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23314step0 raw23314step0Labels permutation80 hz
    mixedMoment B raw23314step1 raw23314step1Labels = mixedMoment B raw23314step2 raw23314step2Labels := by
      have ha : raw23314step2 = (fun i j => raw23314step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23314step2 raw23314step1; decide +kernel
      have hl : raw23314step2Labels = raw23314step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23314step1 raw23314step1Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw23315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23315 raw23315Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw23315 raw23315Labels = mixedMoment B raw23315step0 raw23315step0Labels := by
      have hz : ∀ j, raw23315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23315step0 = (fun i j => raw23315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23315step0 raw23315; decide +kernel
      have hl : raw23315step0Labels = raw23315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23315 raw23315Labels permutation346 hz
    mixedMoment B raw23315step0 raw23315step0Labels = mixedMoment B raw23315step1 raw23315step1Labels := by
      have ha : raw23315step1 = (fun i j => raw23315step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23315step1 raw23315step0; decide +kernel
      have hl : raw23315step1Labels = raw23315step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23315step0 raw23315step0Labels permutation33 permutation2
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw23316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23316 raw23316Labels = mixedMoment B node1990 node1990Labels := by
  calc
    mixedMoment B raw23316 raw23316Labels = mixedMoment B raw23316step0 raw23316step0Labels := by
      have ha : raw23316step0 = (fun i j => raw23316 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23316step0 raw23316; decide +kernel
      have hl : raw23316step0Labels = raw23316Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23316 raw23316Labels permutation183 permutation2
    _ = mixedMoment B node1990 node1990Labels := by rfl

def raw23317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23317 raw23317Labels = mixedMoment B node1918 node1918Labels := by
  calc
    mixedMoment B raw23317 raw23317Labels = mixedMoment B raw23317step0 raw23317step0Labels := by
      have hz : ∀ j, raw23317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23317step0 = (fun i j => raw23317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23317step0 raw23317; decide +kernel
      have hl : raw23317step0Labels = raw23317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23317 raw23317Labels permutation346 hz
    mixedMoment B raw23317step0 raw23317step0Labels = mixedMoment B raw23317step1 raw23317step1Labels := by
      have ha : raw23317step1 = (fun i j => raw23317step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23317step1 raw23317step0; decide +kernel
      have hl : raw23317step1Labels = raw23317step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23317step0 raw23317step0Labels permutation39 permutation2
    _ = mixedMoment B node1918 node1918Labels := by rfl

def raw23318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw23318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw23318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23318 raw23318Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw23318 raw23318Labels = mixedMoment B raw23318step0 raw23318step0Labels := by
      have hz : ∀ j, raw23318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23318step0 = (fun i j => raw23318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23318step0 raw23318; decide +kernel
      have hl : raw23318step0Labels = raw23318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23318 raw23318Labels permutation346 hz
    mixedMoment B raw23318step0 raw23318step0Labels = mixedMoment B raw23318step1 raw23318step1Labels := by
      have ha : raw23318step1 = (fun i j => raw23318step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23318step1 raw23318step0; decide +kernel
      have hl : raw23318step1Labels = raw23318step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23318step0 raw23318step0Labels permutation39 permutation2
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw23319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23319 raw23319Labels = mixedMoment B node573 node573Labels := by
  calc
    mixedMoment B raw23319 raw23319Labels = mixedMoment B raw23319step0 raw23319step0Labels := by
      have hz : ∀ j, raw23319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23319step0 = (fun i j => raw23319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23319step0 raw23319; decide +kernel
      have hl : raw23319step0Labels = raw23319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23319 raw23319Labels permutation346 hz
    mixedMoment B raw23319step0 raw23319step0Labels = mixedMoment B raw23319step1 raw23319step1Labels := by
      have ha : raw23319step1 = (fun i j => raw23319step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23319step1 raw23319step0; decide +kernel
      have hl : raw23319step1Labels = raw23319step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23319step0 raw23319step0Labels permutation39 permutation2
    _ = mixedMoment B node573 node573Labels := by rfl

def raw23320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23320 raw23320Labels = mixedMoment B node901 node901Labels := by
  calc
    mixedMoment B raw23320 raw23320Labels = mixedMoment B raw23320step0 raw23320step0Labels := by
      have ha : raw23320step0 = (fun i j => raw23320 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23320step0 raw23320; decide +kernel
      have hl : raw23320step0Labels = raw23320Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23320 raw23320Labels permutation183 permutation2
    _ = mixedMoment B node901 node901Labels := by rfl

def raw23321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23321 raw23321Labels = mixedMoment B node889 node889Labels := by
  calc
    mixedMoment B raw23321 raw23321Labels = mixedMoment B raw23321step0 raw23321step0Labels := by
      have hz : ∀ j, raw23321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23321step0 = (fun i j => raw23321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23321step0 raw23321; decide +kernel
      have hl : raw23321step0Labels = raw23321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23321 raw23321Labels permutation346 hz
    mixedMoment B raw23321step0 raw23321step0Labels = mixedMoment B raw23321step1 raw23321step1Labels := by
      have ha : raw23321step1 = (fun i j => raw23321step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23321step1 raw23321step0; decide +kernel
      have hl : raw23321step1Labels = raw23321step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23321step0 raw23321step0Labels permutation39 permutation2
    _ = mixedMoment B node889 node889Labels := by rfl

def raw23322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw23322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw23322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23322 raw23322Labels = mixedMoment B node1004 node1004Labels := by
  calc
    mixedMoment B raw23322 raw23322Labels = mixedMoment B raw23322step0 raw23322step0Labels := by
      have hz : ∀ j, raw23322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23322step0 = (fun i j => raw23322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23322step0 raw23322; decide +kernel
      have hl : raw23322step0Labels = raw23322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23322 raw23322Labels permutation346 hz
    mixedMoment B raw23322step0 raw23322step0Labels = mixedMoment B raw23322step1 raw23322step1Labels := by
      have ha : raw23322step1 = (fun i j => raw23322step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23322step1 raw23322step0; decide +kernel
      have hl : raw23322step1Labels = raw23322step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23322step0 raw23322step0Labels permutation39 permutation2
    _ = mixedMoment B node1004 node1004Labels := by rfl

def raw23323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw23323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23323 raw23323Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw23323 raw23323Labels = mixedMoment B raw23323step0 raw23323step0Labels := by
      have ha : raw23323step0 = (fun i j => raw23323 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23323step0 raw23323; decide +kernel
      have hl : raw23323step0Labels = raw23323Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23323 raw23323Labels permutation201 permutation2
    _ = mixedMoment B node866 node866Labels := by rfl

def raw23324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw23324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw23324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw23324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23324 raw23324Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw23324 raw23324Labels = mixedMoment B raw23324step0 raw23324step0Labels := by
      have hz : ∀ j, raw23324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23324step0 = (fun i j => raw23324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23324step0 raw23324; decide +kernel
      have hl : raw23324step0Labels = raw23324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23324 raw23324Labels permutation346 hz
    mixedMoment B raw23324step0 raw23324step0Labels = mixedMoment B raw23324step1 raw23324step1Labels := by
      have ha : raw23324step1 = (fun i j => raw23324step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23324step1 raw23324step0; decide +kernel
      have hl : raw23324step1Labels = raw23324step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23324step0 raw23324step0Labels permutation39 permutation2
    _ = mixedMoment B node873 node873Labels := by rfl

def raw23325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw23325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw23325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw23325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23325 raw23325Labels = mixedMoment B node874 node874Labels := by
  calc
    mixedMoment B raw23325 raw23325Labels = mixedMoment B raw23325step0 raw23325step0Labels := by
      have hz : ∀ j, raw23325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23325step0 = (fun i j => raw23325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23325step0 raw23325; decide +kernel
      have hl : raw23325step0Labels = raw23325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23325 raw23325Labels permutation346 hz
    mixedMoment B raw23325step0 raw23325step0Labels = mixedMoment B raw23325step1 raw23325step1Labels := by
      have ha : raw23325step1 = (fun i j => raw23325step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23325step1 raw23325step0; decide +kernel
      have hl : raw23325step1Labels = raw23325step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23325step0 raw23325step0Labels permutation38 permutation2
    _ = mixedMoment B node874 node874Labels := by rfl

def raw23326 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23326 raw23326Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw23326 raw23326Labels = mixedMoment B raw23326step0 raw23326step0Labels := by
      have hz : ∀ j, raw23326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23326step0 = (fun i j => raw23326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23326step0 raw23326; decide +kernel
      have hl : raw23326step0Labels = raw23326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23326 raw23326Labels permutation346 hz
    mixedMoment B raw23326step0 raw23326step0Labels = mixedMoment B raw23326step1 raw23326step1Labels := by
      have ha : raw23326step1 = (fun i j => raw23326step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23326step1 raw23326step0; decide +kernel
      have hl : raw23326step1Labels = raw23326step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23326step0 raw23326step0Labels permutation39 permutation4
    mixedMoment B raw23326step1 raw23326step1Labels = mixedMoment B raw23326step2 raw23326step2Labels := by
      have ha : raw23326step2 = -raw23326step1 := by apply Matrix.ext; change ∀ i j, raw23326step2 i j = -(raw23326step1 i j); unfold raw23326step2 raw23326step1; decide +kernel
      have hl : raw23326step2Labels = raw23326step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1618 node1618Labels := by rfl

def raw23327 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23327 raw23327Labels = mixedMoment B node724 node724Labels := by
  calc
    mixedMoment B raw23327 raw23327Labels = mixedMoment B raw23327step0 raw23327step0Labels := by
      have hz : ∀ j, raw23327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23327step0 = (fun i j => raw23327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23327step0 raw23327; decide +kernel
      have hl : raw23327step0Labels = raw23327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23327 raw23327Labels permutation346 hz
    mixedMoment B raw23327step0 raw23327step0Labels = mixedMoment B raw23327step1 raw23327step1Labels := by
      have ha : raw23327step1 = (fun i j => raw23327step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23327step1 raw23327step0; decide +kernel
      have hl : raw23327step1Labels = raw23327step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23327step0 raw23327step0Labels permutation42 permutation4
    mixedMoment B raw23327step1 raw23327step1Labels = mixedMoment B raw23327step2 raw23327step2Labels := by
      have ha : raw23327step2 = -raw23327step1 := by apply Matrix.ext; change ∀ i j, raw23327step2 i j = -(raw23327step1 i j); unfold raw23327step2 raw23327step1; decide +kernel
      have hl : raw23327step2Labels = raw23327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node724 node724Labels := by rfl

def raw23328 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23328 raw23328Labels = mixedMoment B node710 node710Labels := by
  calc
    mixedMoment B raw23328 raw23328Labels = mixedMoment B raw23328step0 raw23328step0Labels := by
      have ha : raw23328step0 = (fun i j => raw23328 (permutation201 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23328step0 raw23328; decide +kernel
      have hl : raw23328step0Labels = raw23328Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23328 raw23328Labels permutation201 permutation4
    mixedMoment B raw23328step0 raw23328step0Labels = mixedMoment B raw23328step1 raw23328step1Labels := by
      have ha : raw23328step1 = -raw23328step0 := by apply Matrix.ext; change ∀ i j, raw23328step1 i j = -(raw23328step0 i j); unfold raw23328step1 raw23328step0; decide +kernel
      have hl : raw23328step1Labels = raw23328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node710 node710Labels := by rfl

def raw23329 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23329step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23329step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23329 raw23329Labels = mixedMoment B node852 node852Labels := by
  calc
    mixedMoment B raw23329 raw23329Labels = mixedMoment B raw23329step0 raw23329step0Labels := by
      have hz : ∀ j, raw23329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23329step0 = (fun i j => raw23329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23329step0 raw23329; decide +kernel
      have hl : raw23329step0Labels = raw23329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23329 raw23329Labels permutation434 hz
    mixedMoment B raw23329step0 raw23329step0Labels = mixedMoment B raw23329step1 raw23329step1Labels := by
      have hz : ∀ j, raw23329step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23329step1 = (fun i j => raw23329step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23329step1 raw23329step0; decide +kernel
      have hl : raw23329step1Labels = raw23329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23329step0 raw23329step0Labels permutation80 hz
    mixedMoment B raw23329step1 raw23329step1Labels = mixedMoment B raw23329step2 raw23329step2Labels := by
      have ha : raw23329step2 = (fun i j => raw23329step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23329step2 raw23329step1; decide +kernel
      have hl : raw23329step2Labels = raw23329step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23329step1 raw23329step1Labels permutation9 permutation4
    mixedMoment B raw23329step2 raw23329step2Labels = mixedMoment B raw23329step3 raw23329step3Labels := by
      have ha : raw23329step3 = -raw23329step2 := by apply Matrix.ext; change ∀ i j, raw23329step3 i j = -(raw23329step2 i j); unfold raw23329step3 raw23329step2; decide +kernel
      have hl : raw23329step3Labels = raw23329step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node852 node852Labels := by rfl

def raw23330 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw23330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw23330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw23330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23330 raw23330Labels = mixedMoment B node715 node715Labels := by
  calc
    mixedMoment B raw23330 raw23330Labels = mixedMoment B raw23330step0 raw23330step0Labels := by
      have hz : ∀ j, raw23330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23330step0 = (fun i j => raw23330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23330step0 raw23330; decide +kernel
      have hl : raw23330step0Labels = raw23330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23330 raw23330Labels permutation346 hz
    mixedMoment B raw23330step0 raw23330step0Labels = mixedMoment B raw23330step1 raw23330step1Labels := by
      have ha : raw23330step1 = (fun i j => raw23330step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23330step1 raw23330step0; decide +kernel
      have hl : raw23330step1Labels = raw23330step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23330step0 raw23330step0Labels permutation39 permutation4
    mixedMoment B raw23330step1 raw23330step1Labels = mixedMoment B raw23330step2 raw23330step2Labels := by
      have ha : raw23330step2 = -raw23330step1 := by apply Matrix.ext; change ∀ i j, raw23330step2 i j = -(raw23330step1 i j); unfold raw23330step2 raw23330step1; decide +kernel
      have hl : raw23330step2Labels = raw23330step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node715 node715Labels := by rfl

def raw23331 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw23331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw23331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw23331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23331 raw23331Labels = mixedMoment B node717 node717Labels := by
  calc
    mixedMoment B raw23331 raw23331Labels = mixedMoment B raw23331step0 raw23331step0Labels := by
      have hz : ∀ j, raw23331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23331step0 = (fun i j => raw23331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23331step0 raw23331; decide +kernel
      have hl : raw23331step0Labels = raw23331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23331 raw23331Labels permutation346 hz
    mixedMoment B raw23331step0 raw23331step0Labels = mixedMoment B raw23331step1 raw23331step1Labels := by
      have ha : raw23331step1 = (fun i j => raw23331step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23331step1 raw23331step0; decide +kernel
      have hl : raw23331step1Labels = raw23331step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23331step0 raw23331step0Labels permutation38 permutation4
    mixedMoment B raw23331step1 raw23331step1Labels = mixedMoment B raw23331step2 raw23331step2Labels := by
      have ha : raw23331step2 = -raw23331step1 := by apply Matrix.ext; change ∀ i j, raw23331step2 i j = -(raw23331step1 i j); unfold raw23331step2 raw23331step1; decide +kernel
      have hl : raw23331step2Labels = raw23331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node717 node717Labels := by rfl

def raw23332 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw23332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw23332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23332 raw23332Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw23332 raw23332Labels = mixedMoment B raw23332step0 raw23332step0Labels := by
      have hz : ∀ j, raw23332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23332step0 = (fun i j => raw23332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23332step0 raw23332; decide +kernel
      have hl : raw23332step0Labels = raw23332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23332 raw23332Labels permutation346 hz
    mixedMoment B raw23332step0 raw23332step0Labels = mixedMoment B raw23332step1 raw23332step1Labels := by
      have ha : raw23332step1 = (fun i j => raw23332step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23332step1 raw23332step0; decide +kernel
      have hl : raw23332step1Labels = raw23332step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23332step0 raw23332step0Labels permutation38 permutation4
    mixedMoment B raw23332step1 raw23332step1Labels = mixedMoment B raw23332step2 raw23332step2Labels := by
      have ha : raw23332step2 = -raw23332step1 := by apply Matrix.ext; change ∀ i j, raw23332step2 i j = -(raw23332step1 i j); unfold raw23332step2 raw23332step1; decide +kernel
      have hl : raw23332step2Labels = raw23332step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1618 node1618Labels := by rfl

def raw23333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23333step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23333 raw23333Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw23333 raw23333Labels = mixedMoment B raw23333step0 raw23333step0Labels := by
      have hz : ∀ j, raw23333 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23333step0 = (fun i j => raw23333 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23333step0 raw23333; decide +kernel
      have hl : raw23333step0Labels = raw23333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23333 raw23333Labels permutation434 hz
    mixedMoment B raw23333step0 raw23333step0Labels = mixedMoment B raw23333step1 raw23333step1Labels := by
      have hz : ∀ j, raw23333step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23333step1 = (fun i j => raw23333step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23333step1 raw23333step0; decide +kernel
      have hl : raw23333step1Labels = raw23333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23333step0 raw23333step0Labels permutation80 hz
    mixedMoment B raw23333step1 raw23333step1Labels = mixedMoment B raw23333step2 raw23333step2Labels := by
      have ha : raw23333step2 = (fun i j => raw23333step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23333step2 raw23333step1; decide +kernel
      have hl : raw23333step2Labels = raw23333step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23333step1 raw23333step1Labels permutation9 permutation2
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw23334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23334step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23334 raw23334Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw23334 raw23334Labels = mixedMoment B raw23334step0 raw23334step0Labels := by
      have hz : ∀ j, raw23334 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23334step0 = (fun i j => raw23334 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23334step0 raw23334; decide +kernel
      have hl : raw23334step0Labels = raw23334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23334 raw23334Labels permutation434 hz
    mixedMoment B raw23334step0 raw23334step0Labels = mixedMoment B raw23334step1 raw23334step1Labels := by
      have hz : ∀ j, raw23334step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23334step1 = (fun i j => raw23334step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23334step1 raw23334step0; decide +kernel
      have hl : raw23334step1Labels = raw23334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23334step0 raw23334step0Labels permutation56 hz
    mixedMoment B raw23334step1 raw23334step1Labels = mixedMoment B raw23334step2 raw23334step2Labels := by
      have ha : raw23334step2 = (fun i j => raw23334step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23334step2 raw23334step1; decide +kernel
      have hl : raw23334step2Labels = raw23334step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23334step1 raw23334step1Labels permutation9 permutation2
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw23335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23335step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23335step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23335 raw23335Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw23335 raw23335Labels = mixedMoment B raw23335step0 raw23335step0Labels := by
      have hz : ∀ j, raw23335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23335step0 = (fun i j => raw23335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23335step0 raw23335; decide +kernel
      have hl : raw23335step0Labels = raw23335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23335 raw23335Labels permutation346 hz
    mixedMoment B raw23335step0 raw23335step0Labels = mixedMoment B raw23335step1 raw23335step1Labels := by
      have hz : ∀ j, raw23335step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23335step1 = (fun i j => raw23335step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23335step1 raw23335step0; decide +kernel
      have hl : raw23335step1Labels = raw23335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23335step0 raw23335step0Labels permutation56 hz
    mixedMoment B raw23335step1 raw23335step1Labels = mixedMoment B raw23335step2 raw23335step2Labels := by
      have ha : raw23335step2 = (fun i j => raw23335step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23335step2 raw23335step1; decide +kernel
      have hl : raw23335step2Labels = raw23335step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23335step1 raw23335step1Labels permutation9 permutation2
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw23336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23336step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 1, -3], ![1, -1, 0]]
def raw23336step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23336step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw23336step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23336step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw23336step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23336step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw23336step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23336 raw23336Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw23336 raw23336Labels = mixedMoment B raw23336step0 raw23336step0Labels := by
      have hz : ∀ j, raw23336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23336step0 = (fun i j => raw23336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23336step0 raw23336; decide +kernel
      have hl : raw23336step0Labels = raw23336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23336 raw23336Labels permutation434 hz
    mixedMoment B raw23336step0 raw23336step0Labels = mixedMoment B raw23336step1 raw23336step1Labels := by
      have hz : ∀ j, raw23336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23336step1 = (fun i j => raw23336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23336step1 raw23336step0; decide +kernel
      have hl : raw23336step1Labels = raw23336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23336step0 raw23336step0Labels permutation80 hz
    mixedMoment B raw23336step1 raw23336step1Labels = mixedMoment B raw23336step2 raw23336step2Labels := by
      have hz : ∀ j, raw23336step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23336step2 = (fun i j => raw23336step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23336step2 raw23336step1; decide +kernel
      have hl : raw23336step2Labels = raw23336step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23336step1 raw23336step1Labels permutation14 hz
    mixedMoment B raw23336step2 raw23336step2Labels = mixedMoment B raw23336step3 raw23336step3Labels := by
      have ha : raw23336step3 = (fun i j => raw23336step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23336step3 raw23336step2; decide +kernel
      have hl : raw23336step3Labels = raw23336step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23336step2 raw23336step2Labels permutation3 permutation7
    mixedMoment B raw23336step3 raw23336step3Labels = mixedMoment B raw23336step4 raw23336step4Labels := by
      have ha : raw23336step4 = -raw23336step3 := by apply Matrix.ext; change ∀ i j, raw23336step4 i j = -(raw23336step3 i j); unfold raw23336step4 raw23336step3; decide +kernel
      have hl : raw23336step4Labels = raw23336step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23336step4 raw23336step4Labels = mixedMoment B raw23336step5 raw23336step5Labels := by
      have ha : raw23336step5 = raw23336step4 := by apply Matrix.ext; unfold raw23336step5 raw23336step4; decide +kernel
      have hl : raw23336step4Labels = labelEmbedding10 ∘ raw23336step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23336step4 raw23336step4Labels raw23336step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw23337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23337step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23337 raw23337Labels = mixedMoment B node4179 node4179Labels := by
  calc
    mixedMoment B raw23337 raw23337Labels = mixedMoment B raw23337step0 raw23337step0Labels := by
      have hz : ∀ j, raw23337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23337step0 = (fun i j => raw23337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23337step0 raw23337; decide +kernel
      have hl : raw23337step0Labels = raw23337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23337 raw23337Labels permutation434 hz
    mixedMoment B raw23337step0 raw23337step0Labels = mixedMoment B raw23337step1 raw23337step1Labels := by
      have hz : ∀ j, raw23337step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23337step1 = (fun i j => raw23337step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23337step1 raw23337step0; decide +kernel
      have hl : raw23337step1Labels = raw23337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23337step0 raw23337step0Labels permutation80 hz
    mixedMoment B raw23337step1 raw23337step1Labels = mixedMoment B raw23337step2 raw23337step2Labels := by
      have ha : raw23337step2 = (fun i j => raw23337step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23337step2 raw23337step1; decide +kernel
      have hl : raw23337step2Labels = raw23337step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23337step1 raw23337step1Labels permutation9 permutation2
    _ = mixedMoment B node4179 node4179Labels := by rfl

def raw23338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23338 raw23338Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw23338 raw23338Labels = mixedMoment B raw23338step0 raw23338step0Labels := by
      have hz : ∀ j, raw23338 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23338step0 = (fun i j => raw23338 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23338step0 raw23338; decide +kernel
      have hl : raw23338step0Labels = raw23338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23338 raw23338Labels permutation434 hz
    mixedMoment B raw23338step0 raw23338step0Labels = mixedMoment B raw23338step1 raw23338step1Labels := by
      have ha : raw23338step1 = (fun i j => raw23338step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23338step1 raw23338step0; decide +kernel
      have hl : raw23338step1Labels = raw23338step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23338step0 raw23338step0Labels permutation39 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

def raw23339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23339step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23339 raw23339Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw23339 raw23339Labels = mixedMoment B raw23339step0 raw23339step0Labels := by
      have hz : ∀ j, raw23339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23339step0 = (fun i j => raw23339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23339step0 raw23339; decide +kernel
      have hl : raw23339step0Labels = raw23339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23339 raw23339Labels permutation346 hz
    mixedMoment B raw23339step0 raw23339step0Labels = mixedMoment B raw23339step1 raw23339step1Labels := by
      have ha : raw23339step1 = (fun i j => raw23339step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23339step1 raw23339step0; decide +kernel
      have hl : raw23339step1Labels = raw23339step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23339step0 raw23339step0Labels permutation39 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

def raw23340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23340step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23340 raw23340Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw23340 raw23340Labels = mixedMoment B raw23340step0 raw23340step0Labels := by
      have hz : ∀ j, raw23340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23340step0 = (fun i j => raw23340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23340step0 raw23340; decide +kernel
      have hl : raw23340step0Labels = raw23340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23340 raw23340Labels permutation434 hz
    mixedMoment B raw23340step0 raw23340step0Labels = mixedMoment B raw23340step1 raw23340step1Labels := by
      have hz : ∀ j, raw23340step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23340step1 = (fun i j => raw23340step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23340step1 raw23340step0; decide +kernel
      have hl : raw23340step1Labels = raw23340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23340step0 raw23340step0Labels permutation80 hz
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw23341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23341step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23341 raw23341Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw23341 raw23341Labels = mixedMoment B raw23341step0 raw23341step0Labels := by
      have hz : ∀ j, raw23341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23341step0 = (fun i j => raw23341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23341step0 raw23341; decide +kernel
      have hl : raw23341step0Labels = raw23341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23341 raw23341Labels permutation434 hz
    mixedMoment B raw23341step0 raw23341step0Labels = mixedMoment B raw23341step1 raw23341step1Labels := by
      have hz : ∀ j, raw23341step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23341step1 = (fun i j => raw23341step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23341step1 raw23341step0; decide +kernel
      have hl : raw23341step1Labels = raw23341step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23341step0 raw23341step0Labels permutation80 hz
    mixedMoment B raw23341step1 raw23341step1Labels = mixedMoment B raw23341step2 raw23341step2Labels := by
      have ha : raw23341step2 = (fun i j => raw23341step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23341step2 raw23341step1; decide +kernel
      have hl : raw23341step2Labels = raw23341step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23341step1 raw23341step1Labels permutation9 permutation2
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw23342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23342step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23342step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23342step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23342 raw23342Labels = mixedMoment B node4179 node4179Labels := by
  calc
    mixedMoment B raw23342 raw23342Labels = mixedMoment B raw23342step0 raw23342step0Labels := by
      have hz : ∀ j, raw23342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23342step0 = (fun i j => raw23342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23342step0 raw23342; decide +kernel
      have hl : raw23342step0Labels = raw23342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23342 raw23342Labels permutation434 hz
    mixedMoment B raw23342step0 raw23342step0Labels = mixedMoment B raw23342step1 raw23342step1Labels := by
      have hz : ∀ j, raw23342step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23342step1 = (fun i j => raw23342step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23342step1 raw23342step0; decide +kernel
      have hl : raw23342step1Labels = raw23342step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23342step0 raw23342step0Labels permutation56 hz
    mixedMoment B raw23342step1 raw23342step1Labels = mixedMoment B raw23342step2 raw23342step2Labels := by
      have ha : raw23342step2 = (fun i j => raw23342step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23342step2 raw23342step1; decide +kernel
      have hl : raw23342step2Labels = raw23342step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23342step1 raw23342step1Labels permutation9 permutation2
    _ = mixedMoment B node4179 node4179Labels := by rfl

def raw23343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23343step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23343 raw23343Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw23343 raw23343Labels = mixedMoment B raw23343step0 raw23343step0Labels := by
      have hz : ∀ j, raw23343 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23343step0 = (fun i j => raw23343 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23343step0 raw23343; decide +kernel
      have hl : raw23343step0Labels = raw23343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23343 raw23343Labels permutation434 hz
    mixedMoment B raw23343step0 raw23343step0Labels = mixedMoment B raw23343step1 raw23343step1Labels := by
      have ha : raw23343step1 = (fun i j => raw23343step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23343step1 raw23343step0; decide +kernel
      have hl : raw23343step1Labels = raw23343step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23343step0 raw23343step0Labels permutation33 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

def raw23344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23344 raw23344Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw23344 raw23344Labels = mixedMoment B raw23344step0 raw23344step0Labels := by
      have hz : ∀ j, raw23344 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23344step0 = (fun i j => raw23344 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23344step0 raw23344; decide +kernel
      have hl : raw23344step0Labels = raw23344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23344 raw23344Labels permutation265 hz
    mixedMoment B raw23344step0 raw23344step0Labels = mixedMoment B raw23344step1 raw23344step1Labels := by
      have ha : raw23344step1 = (fun i j => raw23344step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23344step1 raw23344step0; decide +kernel
      have hl : raw23344step1Labels = raw23344step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23344step0 raw23344step0Labels permutation39 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

def raw23345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23345step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23345 raw23345Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw23345 raw23345Labels = mixedMoment B raw23345step0 raw23345step0Labels := by
      have hz : ∀ j, raw23345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23345step0 = (fun i j => raw23345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23345step0 raw23345; decide +kernel
      have hl : raw23345step0Labels = raw23345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23345 raw23345Labels permutation434 hz
    mixedMoment B raw23345step0 raw23345step0Labels = mixedMoment B raw23345step1 raw23345step1Labels := by
      have hz : ∀ j, raw23345step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23345step1 = (fun i j => raw23345step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23345step1 raw23345step0; decide +kernel
      have hl : raw23345step1Labels = raw23345step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23345step0 raw23345step0Labels permutation56 hz
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw23346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23346step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23346step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23346 raw23346Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw23346 raw23346Labels = mixedMoment B raw23346step0 raw23346step0Labels := by
      have hz : ∀ j, raw23346 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23346step0 = (fun i j => raw23346 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23346step0 raw23346; decide +kernel
      have hl : raw23346step0Labels = raw23346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23346 raw23346Labels permutation434 hz
    mixedMoment B raw23346step0 raw23346step0Labels = mixedMoment B raw23346step1 raw23346step1Labels := by
      have hz : ∀ j, raw23346step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23346step1 = (fun i j => raw23346step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23346step1 raw23346step0; decide +kernel
      have hl : raw23346step1Labels = raw23346step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23346step0 raw23346step0Labels permutation56 hz
    mixedMoment B raw23346step1 raw23346step1Labels = mixedMoment B raw23346step2 raw23346step2Labels := by
      have ha : raw23346step2 = (fun i j => raw23346step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23346step2 raw23346step1; decide +kernel
      have hl : raw23346step2Labels = raw23346step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23346step1 raw23346step1Labels permutation9 permutation2
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw23347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23347step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23347step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23347 raw23347Labels = mixedMoment B node4179 node4179Labels := by
  calc
    mixedMoment B raw23347 raw23347Labels = mixedMoment B raw23347step0 raw23347step0Labels := by
      have hz : ∀ j, raw23347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23347step0 = (fun i j => raw23347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23347step0 raw23347; decide +kernel
      have hl : raw23347step0Labels = raw23347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23347 raw23347Labels permutation346 hz
    mixedMoment B raw23347step0 raw23347step0Labels = mixedMoment B raw23347step1 raw23347step1Labels := by
      have hz : ∀ j, raw23347step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23347step1 = (fun i j => raw23347step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23347step1 raw23347step0; decide +kernel
      have hl : raw23347step1Labels = raw23347step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23347step0 raw23347step0Labels permutation56 hz
    mixedMoment B raw23347step1 raw23347step1Labels = mixedMoment B raw23347step2 raw23347step2Labels := by
      have ha : raw23347step2 = (fun i j => raw23347step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23347step2 raw23347step1; decide +kernel
      have hl : raw23347step2Labels = raw23347step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23347step1 raw23347step1Labels permutation9 permutation2
    _ = mixedMoment B node4179 node4179Labels := by rfl

def raw23348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23348step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23348 raw23348Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw23348 raw23348Labels = mixedMoment B raw23348step0 raw23348step0Labels := by
      have hz : ∀ j, raw23348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23348step0 = (fun i j => raw23348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23348step0 raw23348; decide +kernel
      have hl : raw23348step0Labels = raw23348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23348 raw23348Labels permutation346 hz
    mixedMoment B raw23348step0 raw23348step0Labels = mixedMoment B raw23348step1 raw23348step1Labels := by
      have ha : raw23348step1 = (fun i j => raw23348step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23348step1 raw23348step0; decide +kernel
      have hl : raw23348step1Labels = raw23348step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23348step0 raw23348step0Labels permutation33 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

def raw23349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23349 raw23349Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw23349 raw23349Labels = mixedMoment B raw23349step0 raw23349step0Labels := by
      have hz : ∀ j, raw23349 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23349step0 = (fun i j => raw23349 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23349step0 raw23349; decide +kernel
      have hl : raw23349step0Labels = raw23349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23349 raw23349Labels permutation265 hz
    mixedMoment B raw23349step0 raw23349step0Labels = mixedMoment B raw23349step1 raw23349step1Labels := by
      have ha : raw23349step1 = (fun i j => raw23349step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23349step1 raw23349step0; decide +kernel
      have hl : raw23349step1Labels = raw23349step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23349step0 raw23349step0Labels permutation33 permutation2
    _ = mixedMoment B node4348 node4348Labels := by rfl

def raw23350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23350 raw23350Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw23350 raw23350Labels = mixedMoment B raw23350step0 raw23350step0Labels := by
      have hz : ∀ j, raw23350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23350step0 = (fun i j => raw23350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23350step0 raw23350; decide +kernel
      have hl : raw23350step0Labels = raw23350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23350 raw23350Labels permutation346 hz
    mixedMoment B raw23350step0 raw23350step0Labels = mixedMoment B raw23350step1 raw23350step1Labels := by
      have hz : ∀ j, raw23350step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23350step1 = (fun i j => raw23350step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23350step1 raw23350step0; decide +kernel
      have hl : raw23350step1Labels = raw23350step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23350step0 raw23350step0Labels permutation56 hz
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw23351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23351step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23351step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23351step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23351step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23351 raw23351Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw23351 raw23351Labels = mixedMoment B raw23351step0 raw23351step0Labels := by
      have hz : ∀ j, raw23351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23351step0 = (fun i j => raw23351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23351step0 raw23351; decide +kernel
      have hl : raw23351step0Labels = raw23351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23351 raw23351Labels permutation346 hz
    mixedMoment B raw23351step0 raw23351step0Labels = mixedMoment B raw23351step1 raw23351step1Labels := by
      have hz : ∀ j, raw23351step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23351step1 = (fun i j => raw23351step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23351step1 raw23351step0; decide +kernel
      have hl : raw23351step1Labels = raw23351step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23351step0 raw23351step0Labels permutation56 hz
    mixedMoment B raw23351step1 raw23351step1Labels = mixedMoment B raw23351step2 raw23351step2Labels := by
      have ha : raw23351step2 = (fun i j => raw23351step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23351step2 raw23351step1; decide +kernel
      have hl : raw23351step2Labels = raw23351step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23351step1 raw23351step1Labels permutation9 permutation2
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw23352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, 0, -3], ![2, -2, 0]]
def raw23352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23352step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw23352step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23352 raw23352Labels = mixedMoment B node4190 node4190Labels := by
  calc
    mixedMoment B raw23352 raw23352Labels = mixedMoment B raw23352step0 raw23352step0Labels := by
      have hz : ∀ j, raw23352 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23352step0 = (fun i j => raw23352 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23352step0 raw23352; decide +kernel
      have hl : raw23352step0Labels = raw23352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23352 raw23352Labels permutation434 hz
    mixedMoment B raw23352step0 raw23352step0Labels = mixedMoment B raw23352step1 raw23352step1Labels := by
      have hz : ∀ j, raw23352step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23352step1 = (fun i j => raw23352step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23352step1 raw23352step0; decide +kernel
      have hl : raw23352step1Labels = raw23352step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23352step0 raw23352step0Labels permutation80 hz
    mixedMoment B raw23352step1 raw23352step1Labels = mixedMoment B raw23352step2 raw23352step2Labels := by
      have hz : ∀ j, raw23352step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23352step2 = (fun i j => raw23352step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23352step2 raw23352step1; decide +kernel
      have hl : raw23352step2Labels = raw23352step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23352step1 raw23352step1Labels permutation14 hz
    mixedMoment B raw23352step2 raw23352step2Labels = mixedMoment B raw23352step3 raw23352step3Labels := by
      have ha : raw23352step3 = (fun i j => raw23352step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23352step3 raw23352step2; decide +kernel
      have hl : raw23352step3Labels = raw23352step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23352step2 raw23352step2Labels permutation3 permutation2
    _ = mixedMoment B node4190 node4190Labels := by rfl

def raw23353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23353step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23353step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23353 raw23353Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw23353 raw23353Labels = mixedMoment B raw23353step0 raw23353step0Labels := by
      have hz : ∀ j, raw23353 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23353step0 = (fun i j => raw23353 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23353step0 raw23353; decide +kernel
      have hl : raw23353step0Labels = raw23353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23353 raw23353Labels permutation434 hz
    mixedMoment B raw23353step0 raw23353step0Labels = mixedMoment B raw23353step1 raw23353step1Labels := by
      have hz : ∀ j, raw23353step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23353step1 = (fun i j => raw23353step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23353step1 raw23353step0; decide +kernel
      have hl : raw23353step1Labels = raw23353step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23353step0 raw23353step0Labels permutation80 hz
    mixedMoment B raw23353step1 raw23353step1Labels = mixedMoment B raw23353step2 raw23353step2Labels := by
      have ha : raw23353step2 = (fun i j => raw23353step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23353step2 raw23353step1; decide +kernel
      have hl : raw23353step2Labels = raw23353step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23353step1 raw23353step1Labels permutation9 permutation2
    _ = mixedMoment B node4359 node4359Labels := by rfl

def raw23354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23354step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23354 raw23354Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw23354 raw23354Labels = mixedMoment B raw23354step0 raw23354step0Labels := by
      have hz : ∀ j, raw23354 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23354step0 = (fun i j => raw23354 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23354step0 raw23354; decide +kernel
      have hl : raw23354step0Labels = raw23354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23354 raw23354Labels permutation434 hz
    mixedMoment B raw23354step0 raw23354step0Labels = mixedMoment B raw23354step1 raw23354step1Labels := by
      have hz : ∀ j, raw23354step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23354step1 = (fun i j => raw23354step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23354step1 raw23354step0; decide +kernel
      have hl : raw23354step1Labels = raw23354step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23354step0 raw23354step0Labels permutation56 hz
    mixedMoment B raw23354step1 raw23354step1Labels = mixedMoment B raw23354step2 raw23354step2Labels := by
      have ha : raw23354step2 = (fun i j => raw23354step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23354step2 raw23354step1; decide +kernel
      have hl : raw23354step2Labels = raw23354step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23354step1 raw23354step1Labels permutation9 permutation2
    _ = mixedMoment B node4359 node4359Labels := by rfl

def raw23355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23355step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23355 raw23355Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw23355 raw23355Labels = mixedMoment B raw23355step0 raw23355step0Labels := by
      have hz : ∀ j, raw23355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23355step0 = (fun i j => raw23355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23355step0 raw23355; decide +kernel
      have hl : raw23355step0Labels = raw23355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23355 raw23355Labels permutation346 hz
    mixedMoment B raw23355step0 raw23355step0Labels = mixedMoment B raw23355step1 raw23355step1Labels := by
      have hz : ∀ j, raw23355step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23355step1 = (fun i j => raw23355step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23355step1 raw23355step0; decide +kernel
      have hl : raw23355step1Labels = raw23355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23355step0 raw23355step0Labels permutation56 hz
    mixedMoment B raw23355step1 raw23355step1Labels = mixedMoment B raw23355step2 raw23355step2Labels := by
      have ha : raw23355step2 = (fun i j => raw23355step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23355step2 raw23355step1; decide +kernel
      have hl : raw23355step2Labels = raw23355step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23355step1 raw23355step1Labels permutation9 permutation2
    _ = mixedMoment B node4359 node4359Labels := by rfl

def raw23356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23356step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, 0, -3], ![1, -1, 0]]
def raw23356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23356step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw23356step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23356 raw23356Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw23356 raw23356Labels = mixedMoment B raw23356step0 raw23356step0Labels := by
      have hz : ∀ j, raw23356 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23356step0 = (fun i j => raw23356 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23356step0 raw23356; decide +kernel
      have hl : raw23356step0Labels = raw23356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23356 raw23356Labels permutation434 hz
    mixedMoment B raw23356step0 raw23356step0Labels = mixedMoment B raw23356step1 raw23356step1Labels := by
      have hz : ∀ j, raw23356step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23356step1 = (fun i j => raw23356step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23356step1 raw23356step0; decide +kernel
      have hl : raw23356step1Labels = raw23356step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23356step0 raw23356step0Labels permutation80 hz
    mixedMoment B raw23356step1 raw23356step1Labels = mixedMoment B raw23356step2 raw23356step2Labels := by
      have hz : ∀ j, raw23356step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23356step2 = (fun i j => raw23356step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23356step2 raw23356step1; decide +kernel
      have hl : raw23356step2Labels = raw23356step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23356step1 raw23356step1Labels permutation14 hz
    mixedMoment B raw23356step2 raw23356step2Labels = mixedMoment B raw23356step3 raw23356step3Labels := by
      have ha : raw23356step3 = (fun i j => raw23356step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23356step3 raw23356step2; decide +kernel
      have hl : raw23356step3Labels = raw23356step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23356step2 raw23356step2Labels permutation3 permutation2
    _ = mixedMoment B node4501 node4501Labels := by rfl

def raw23357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23357step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23357step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw23357step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23357 raw23357Labels = mixedMoment B node4193 node4193Labels := by
  calc
    mixedMoment B raw23357 raw23357Labels = mixedMoment B raw23357step0 raw23357step0Labels := by
      have hz : ∀ j, raw23357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23357step0 = (fun i j => raw23357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23357step0 raw23357; decide +kernel
      have hl : raw23357step0Labels = raw23357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23357 raw23357Labels permutation434 hz
    mixedMoment B raw23357step0 raw23357step0Labels = mixedMoment B raw23357step1 raw23357step1Labels := by
      have hz : ∀ j, raw23357step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23357step1 = (fun i j => raw23357step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23357step1 raw23357step0; decide +kernel
      have hl : raw23357step1Labels = raw23357step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23357step0 raw23357step0Labels permutation80 hz
    mixedMoment B raw23357step1 raw23357step1Labels = mixedMoment B raw23357step2 raw23357step2Labels := by
      have hz : ∀ j, raw23357step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23357step2 = (fun i j => raw23357step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23357step2 raw23357step1; decide +kernel
      have hl : raw23357step2Labels = raw23357step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23357step1 raw23357step1Labels permutation14 hz
    _ = mixedMoment B node4193 node4193Labels := by rfl

def raw23358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23358step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23358 raw23358Labels = mixedMoment B node4362 node4362Labels := by
  calc
    mixedMoment B raw23358 raw23358Labels = mixedMoment B raw23358step0 raw23358step0Labels := by
      have hz : ∀ j, raw23358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23358step0 = (fun i j => raw23358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23358step0 raw23358; decide +kernel
      have hl : raw23358step0Labels = raw23358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23358 raw23358Labels permutation434 hz
    mixedMoment B raw23358step0 raw23358step0Labels = mixedMoment B raw23358step1 raw23358step1Labels := by
      have hz : ∀ j, raw23358step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23358step1 = (fun i j => raw23358step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23358step1 raw23358step0; decide +kernel
      have hl : raw23358step1Labels = raw23358step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23358step0 raw23358step0Labels permutation80 hz
    _ = mixedMoment B node4362 node4362Labels := by rfl

def raw23359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23359 raw23359Labels = mixedMoment B node4362 node4362Labels := by
  calc
    mixedMoment B raw23359 raw23359Labels = mixedMoment B raw23359step0 raw23359step0Labels := by
      have hz : ∀ j, raw23359 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23359step0 = (fun i j => raw23359 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23359step0 raw23359; decide +kernel
      have hl : raw23359step0Labels = raw23359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23359 raw23359Labels permutation434 hz
    mixedMoment B raw23359step0 raw23359step0Labels = mixedMoment B raw23359step1 raw23359step1Labels := by
      have hz : ∀ j, raw23359step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23359step1 = (fun i j => raw23359step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23359step1 raw23359step0; decide +kernel
      have hl : raw23359step1Labels = raw23359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23359step0 raw23359step0Labels permutation56 hz
    _ = mixedMoment B node4362 node4362Labels := by rfl

def raw23360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23360 raw23360Labels = mixedMoment B node4362 node4362Labels := by
  calc
    mixedMoment B raw23360 raw23360Labels = mixedMoment B raw23360step0 raw23360step0Labels := by
      have hz : ∀ j, raw23360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23360step0 = (fun i j => raw23360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23360step0 raw23360; decide +kernel
      have hl : raw23360step0Labels = raw23360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23360 raw23360Labels permutation346 hz
    mixedMoment B raw23360step0 raw23360step0Labels = mixedMoment B raw23360step1 raw23360step1Labels := by
      have hz : ∀ j, raw23360step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23360step1 = (fun i j => raw23360step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23360step1 raw23360step0; decide +kernel
      have hl : raw23360step1Labels = raw23360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23360step0 raw23360step0Labels permutation56 hz
    _ = mixedMoment B node4362 node4362Labels := by rfl

def raw23361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23361step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw23361step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23361 raw23361Labels = mixedMoment B node3095 node3095Labels := by
  calc
    mixedMoment B raw23361 raw23361Labels = mixedMoment B raw23361step0 raw23361step0Labels := by
      have hz : ∀ j, raw23361 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23361step0 = (fun i j => raw23361 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23361step0 raw23361; decide +kernel
      have hl : raw23361step0Labels = raw23361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23361 raw23361Labels permutation434 hz
    mixedMoment B raw23361step0 raw23361step0Labels = mixedMoment B raw23361step1 raw23361step1Labels := by
      have hz : ∀ j, raw23361step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23361step1 = (fun i j => raw23361step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23361step1 raw23361step0; decide +kernel
      have hl : raw23361step1Labels = raw23361step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23361step0 raw23361step0Labels permutation80 hz
    mixedMoment B raw23361step1 raw23361step1Labels = mixedMoment B raw23361step2 raw23361step2Labels := by
      have ha : raw23361step2 = (fun i j => raw23361step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23361step2 raw23361step1; decide +kernel
      have hl : raw23361step2Labels = raw23361step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23361step1 raw23361step1Labels permutation23 permutation6
    _ = mixedMoment B node3095 node3095Labels := by rfl

def raw23362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23362step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw23362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23362 raw23362Labels = mixedMoment B node3095 node3095Labels := by
  calc
    mixedMoment B raw23362 raw23362Labels = mixedMoment B raw23362step0 raw23362step0Labels := by
      have hz : ∀ j, raw23362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23362step0 = (fun i j => raw23362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23362step0 raw23362; decide +kernel
      have hl : raw23362step0Labels = raw23362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23362 raw23362Labels permutation434 hz
    mixedMoment B raw23362step0 raw23362step0Labels = mixedMoment B raw23362step1 raw23362step1Labels := by
      have hz : ∀ j, raw23362step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23362step1 = (fun i j => raw23362step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23362step1 raw23362step0; decide +kernel
      have hl : raw23362step1Labels = raw23362step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23362step0 raw23362step0Labels permutation56 hz
    mixedMoment B raw23362step1 raw23362step1Labels = mixedMoment B raw23362step2 raw23362step2Labels := by
      have ha : raw23362step2 = (fun i j => raw23362step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23362step2 raw23362step1; decide +kernel
      have hl : raw23362step2Labels = raw23362step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23362step1 raw23362step1Labels permutation23 permutation6
    _ = mixedMoment B node3095 node3095Labels := by rfl

def raw23363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23363step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23363step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw23363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23363 raw23363Labels = mixedMoment B node3095 node3095Labels := by
  calc
    mixedMoment B raw23363 raw23363Labels = mixedMoment B raw23363step0 raw23363step0Labels := by
      have hz : ∀ j, raw23363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23363step0 = (fun i j => raw23363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23363step0 raw23363; decide +kernel
      have hl : raw23363step0Labels = raw23363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23363 raw23363Labels permutation346 hz
    mixedMoment B raw23363step0 raw23363step0Labels = mixedMoment B raw23363step1 raw23363step1Labels := by
      have hz : ∀ j, raw23363step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23363step1 = (fun i j => raw23363step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23363step1 raw23363step0; decide +kernel
      have hl : raw23363step1Labels = raw23363step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23363step0 raw23363step0Labels permutation56 hz
    mixedMoment B raw23363step1 raw23363step1Labels = mixedMoment B raw23363step2 raw23363step2Labels := by
      have ha : raw23363step2 = (fun i j => raw23363step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23363step2 raw23363step1; decide +kernel
      have hl : raw23363step2Labels = raw23363step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23363step1 raw23363step1Labels permutation23 permutation6
    _ = mixedMoment B node3095 node3095Labels := by rfl

def raw23364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23364step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23364step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 1, -3], ![1, -1, 0]]
def raw23364step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23364step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw23364step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23364 raw23364Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw23364 raw23364Labels = mixedMoment B raw23364step0 raw23364step0Labels := by
      have hz : ∀ j, raw23364 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23364step0 = (fun i j => raw23364 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23364step0 raw23364; decide +kernel
      have hl : raw23364step0Labels = raw23364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23364 raw23364Labels permutation434 hz
    mixedMoment B raw23364step0 raw23364step0Labels = mixedMoment B raw23364step1 raw23364step1Labels := by
      have hz : ∀ j, raw23364step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23364step1 = (fun i j => raw23364step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23364step1 raw23364step0; decide +kernel
      have hl : raw23364step1Labels = raw23364step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23364step0 raw23364step0Labels permutation80 hz
    mixedMoment B raw23364step1 raw23364step1Labels = mixedMoment B raw23364step2 raw23364step2Labels := by
      have hz : ∀ j, raw23364step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23364step2 = (fun i j => raw23364step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23364step2 raw23364step1; decide +kernel
      have hl : raw23364step2Labels = raw23364step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23364step1 raw23364step1Labels permutation14 hz
    mixedMoment B raw23364step2 raw23364step2Labels = mixedMoment B raw23364step3 raw23364step3Labels := by
      have ha : raw23364step3 = (fun i j => raw23364step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23364step3 raw23364step2; decide +kernel
      have hl : raw23364step3Labels = raw23364step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23364step2 raw23364step2Labels permutation5 permutation6
    _ = mixedMoment B node3114 node3114Labels := by rfl

def raw23365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23365step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23365step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23365 raw23365Labels = mixedMoment B node653 node653Labels := by
  calc
    mixedMoment B raw23365 raw23365Labels = mixedMoment B raw23365step0 raw23365step0Labels := by
      have hz : ∀ j, raw23365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23365step0 = (fun i j => raw23365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23365step0 raw23365; decide +kernel
      have hl : raw23365step0Labels = raw23365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23365 raw23365Labels permutation434 hz
    mixedMoment B raw23365step0 raw23365step0Labels = mixedMoment B raw23365step1 raw23365step1Labels := by
      have hz : ∀ j, raw23365step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23365step1 = (fun i j => raw23365step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23365step1 raw23365step0; decide +kernel
      have hl : raw23365step1Labels = raw23365step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23365step0 raw23365step0Labels permutation80 hz
    mixedMoment B raw23365step1 raw23365step1Labels = mixedMoment B raw23365step2 raw23365step2Labels := by
      have ha : raw23365step2 = (fun i j => raw23365step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23365step2 raw23365step1; decide +kernel
      have hl : raw23365step2Labels = raw23365step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23365step1 raw23365step1Labels permutation8 permutation3
    _ = mixedMoment B node653 node653Labels := by rfl

def raw23366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23366 raw23366Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw23366 raw23366Labels = mixedMoment B raw23366step0 raw23366step0Labels := by
      have hz : ∀ j, raw23366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23366step0 = (fun i j => raw23366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23366step0 raw23366; decide +kernel
      have hl : raw23366step0Labels = raw23366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23366 raw23366Labels permutation434 hz
    mixedMoment B raw23366step0 raw23366step0Labels = mixedMoment B raw23366step1 raw23366step1Labels := by
      have ha : raw23366step1 = (fun i j => raw23366step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23366step1 raw23366step0; decide +kernel
      have hl : raw23366step1Labels = raw23366step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23366step0 raw23366step0Labels permutation38 permutation3
    _ = mixedMoment B node1347 node1347Labels := by rfl

def raw23367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23367 raw23367Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw23367 raw23367Labels = mixedMoment B raw23367step0 raw23367step0Labels := by
      have hz : ∀ j, raw23367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23367step0 = (fun i j => raw23367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23367step0 raw23367; decide +kernel
      have hl : raw23367step0Labels = raw23367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23367 raw23367Labels permutation346 hz
    mixedMoment B raw23367step0 raw23367step0Labels = mixedMoment B raw23367step1 raw23367step1Labels := by
      have ha : raw23367step1 = (fun i j => raw23367step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23367step1 raw23367step0; decide +kernel
      have hl : raw23367step1Labels = raw23367step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23367step0 raw23367step0Labels permutation38 permutation3
    _ = mixedMoment B node1347 node1347Labels := by rfl

def raw23368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23368step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23368step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23368 raw23368Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw23368 raw23368Labels = mixedMoment B raw23368step0 raw23368step0Labels := by
      have hz : ∀ j, raw23368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23368step0 = (fun i j => raw23368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23368step0 raw23368; decide +kernel
      have hl : raw23368step0Labels = raw23368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23368 raw23368Labels permutation434 hz
    mixedMoment B raw23368step0 raw23368step0Labels = mixedMoment B raw23368step1 raw23368step1Labels := by
      have hz : ∀ j, raw23368step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23368step1 = (fun i j => raw23368step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23368step1 raw23368step0; decide +kernel
      have hl : raw23368step1Labels = raw23368step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23368step0 raw23368step0Labels permutation80 hz
    mixedMoment B raw23368step1 raw23368step1Labels = mixedMoment B raw23368step2 raw23368step2Labels := by
      have ha : raw23368step2 = (fun i j => raw23368step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23368step2 raw23368step1; decide +kernel
      have hl : raw23368step2Labels = raw23368step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23368step1 raw23368step1Labels permutation10 permutation3
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw23369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23369step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23369step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23369step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23369 raw23369Labels = mixedMoment B node1451 node1451Labels := by
  calc
    mixedMoment B raw23369 raw23369Labels = mixedMoment B raw23369step0 raw23369step0Labels := by
      have hz : ∀ j, raw23369 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23369step0 = (fun i j => raw23369 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23369step0 raw23369; decide +kernel
      have hl : raw23369step0Labels = raw23369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23369 raw23369Labels permutation434 hz
    mixedMoment B raw23369step0 raw23369step0Labels = mixedMoment B raw23369step1 raw23369step1Labels := by
      have hz : ∀ j, raw23369step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23369step1 = (fun i j => raw23369step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23369step1 raw23369step0; decide +kernel
      have hl : raw23369step1Labels = raw23369step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23369step0 raw23369step0Labels permutation80 hz
    mixedMoment B raw23369step1 raw23369step1Labels = mixedMoment B raw23369step2 raw23369step2Labels := by
      have ha : raw23369step2 = (fun i j => raw23369step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23369step2 raw23369step1; decide +kernel
      have hl : raw23369step2Labels = raw23369step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23369step1 raw23369step1Labels permutation9 permutation3
    _ = mixedMoment B node1451 node1451Labels := by rfl

def raw23370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23370step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23370step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23370 raw23370Labels = mixedMoment B node653 node653Labels := by
  calc
    mixedMoment B raw23370 raw23370Labels = mixedMoment B raw23370step0 raw23370step0Labels := by
      have hz : ∀ j, raw23370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23370step0 = (fun i j => raw23370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23370step0 raw23370; decide +kernel
      have hl : raw23370step0Labels = raw23370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23370 raw23370Labels permutation434 hz
    mixedMoment B raw23370step0 raw23370step0Labels = mixedMoment B raw23370step1 raw23370step1Labels := by
      have hz : ∀ j, raw23370step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23370step1 = (fun i j => raw23370step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23370step1 raw23370step0; decide +kernel
      have hl : raw23370step1Labels = raw23370step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23370step0 raw23370step0Labels permutation56 hz
    mixedMoment B raw23370step1 raw23370step1Labels = mixedMoment B raw23370step2 raw23370step2Labels := by
      have ha : raw23370step2 = (fun i j => raw23370step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23370step2 raw23370step1; decide +kernel
      have hl : raw23370step2Labels = raw23370step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23370step1 raw23370step1Labels permutation8 permutation3
    _ = mixedMoment B node653 node653Labels := by rfl

def raw23371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23371 raw23371Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw23371 raw23371Labels = mixedMoment B raw23371step0 raw23371step0Labels := by
      have hz : ∀ j, raw23371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23371step0 = (fun i j => raw23371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23371step0 raw23371; decide +kernel
      have hl : raw23371step0Labels = raw23371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23371 raw23371Labels permutation434 hz
    mixedMoment B raw23371step0 raw23371step0Labels = mixedMoment B raw23371step1 raw23371step1Labels := by
      have ha : raw23371step1 = (fun i j => raw23371step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23371step1 raw23371step0; decide +kernel
      have hl : raw23371step1Labels = raw23371step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23371step0 raw23371step0Labels permutation32 permutation3
    _ = mixedMoment B node1347 node1347Labels := by rfl

def raw23372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23372 raw23372Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw23372 raw23372Labels = mixedMoment B raw23372step0 raw23372step0Labels := by
      have hz : ∀ j, raw23372 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23372step0 = (fun i j => raw23372 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23372step0 raw23372; decide +kernel
      have hl : raw23372step0Labels = raw23372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23372 raw23372Labels permutation265 hz
    mixedMoment B raw23372step0 raw23372step0Labels = mixedMoment B raw23372step1 raw23372step1Labels := by
      have ha : raw23372step1 = (fun i j => raw23372step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23372step1 raw23372step0; decide +kernel
      have hl : raw23372step1Labels = raw23372step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23372step0 raw23372step0Labels permutation38 permutation3
    _ = mixedMoment B node1347 node1347Labels := by rfl

def raw23373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23373step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23373step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23373 raw23373Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw23373 raw23373Labels = mixedMoment B raw23373step0 raw23373step0Labels := by
      have hz : ∀ j, raw23373 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23373step0 = (fun i j => raw23373 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23373step0 raw23373; decide +kernel
      have hl : raw23373step0Labels = raw23373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23373 raw23373Labels permutation434 hz
    mixedMoment B raw23373step0 raw23373step0Labels = mixedMoment B raw23373step1 raw23373step1Labels := by
      have hz : ∀ j, raw23373step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23373step1 = (fun i j => raw23373step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23373step1 raw23373step0; decide +kernel
      have hl : raw23373step1Labels = raw23373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23373step0 raw23373step0Labels permutation56 hz
    mixedMoment B raw23373step1 raw23373step1Labels = mixedMoment B raw23373step2 raw23373step2Labels := by
      have ha : raw23373step2 = (fun i j => raw23373step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23373step2 raw23373step1; decide +kernel
      have hl : raw23373step2Labels = raw23373step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23373step1 raw23373step1Labels permutation10 permutation3
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw23374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23374step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23374 raw23374Labels = mixedMoment B node1451 node1451Labels := by
  calc
    mixedMoment B raw23374 raw23374Labels = mixedMoment B raw23374step0 raw23374step0Labels := by
      have hz : ∀ j, raw23374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23374step0 = (fun i j => raw23374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23374step0 raw23374; decide +kernel
      have hl : raw23374step0Labels = raw23374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23374 raw23374Labels permutation434 hz
    mixedMoment B raw23374step0 raw23374step0Labels = mixedMoment B raw23374step1 raw23374step1Labels := by
      have hz : ∀ j, raw23374step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23374step1 = (fun i j => raw23374step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23374step1 raw23374step0; decide +kernel
      have hl : raw23374step1Labels = raw23374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23374step0 raw23374step0Labels permutation56 hz
    mixedMoment B raw23374step1 raw23374step1Labels = mixedMoment B raw23374step2 raw23374step2Labels := by
      have ha : raw23374step2 = (fun i j => raw23374step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23374step2 raw23374step1; decide +kernel
      have hl : raw23374step2Labels = raw23374step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23374step1 raw23374step1Labels permutation9 permutation3
    _ = mixedMoment B node1451 node1451Labels := by rfl

def raw23375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23375 raw23375Labels = mixedMoment B node653 node653Labels := by
  calc
    mixedMoment B raw23375 raw23375Labels = mixedMoment B raw23375step0 raw23375step0Labels := by
      have hz : ∀ j, raw23375 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23375step0 = (fun i j => raw23375 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23375step0 raw23375; decide +kernel
      have hl : raw23375step0Labels = raw23375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23375 raw23375Labels permutation346 hz
    mixedMoment B raw23375step0 raw23375step0Labels = mixedMoment B raw23375step1 raw23375step1Labels := by
      have hz : ∀ j, raw23375step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23375step1 = (fun i j => raw23375step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23375step1 raw23375step0; decide +kernel
      have hl : raw23375step1Labels = raw23375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23375step0 raw23375step0Labels permutation56 hz
    mixedMoment B raw23375step1 raw23375step1Labels = mixedMoment B raw23375step2 raw23375step2Labels := by
      have ha : raw23375step2 = (fun i j => raw23375step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23375step2 raw23375step1; decide +kernel
      have hl : raw23375step2Labels = raw23375step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23375step1 raw23375step1Labels permutation8 permutation3
    _ = mixedMoment B node653 node653Labels := by rfl

def raw23376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23376 raw23376Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw23376 raw23376Labels = mixedMoment B raw23376step0 raw23376step0Labels := by
      have hz : ∀ j, raw23376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23376step0 = (fun i j => raw23376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23376step0 raw23376; decide +kernel
      have hl : raw23376step0Labels = raw23376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23376 raw23376Labels permutation346 hz
    mixedMoment B raw23376step0 raw23376step0Labels = mixedMoment B raw23376step1 raw23376step1Labels := by
      have ha : raw23376step1 = (fun i j => raw23376step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23376step1 raw23376step0; decide +kernel
      have hl : raw23376step1Labels = raw23376step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23376step0 raw23376step0Labels permutation32 permutation3
    _ = mixedMoment B node1347 node1347Labels := by rfl

def raw23377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23377 raw23377Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw23377 raw23377Labels = mixedMoment B raw23377step0 raw23377step0Labels := by
      have hz : ∀ j, raw23377 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23377step0 = (fun i j => raw23377 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23377step0 raw23377; decide +kernel
      have hl : raw23377step0Labels = raw23377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23377 raw23377Labels permutation265 hz
    mixedMoment B raw23377step0 raw23377step0Labels = mixedMoment B raw23377step1 raw23377step1Labels := by
      have ha : raw23377step1 = (fun i j => raw23377step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23377step1 raw23377step0; decide +kernel
      have hl : raw23377step1Labels = raw23377step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23377step0 raw23377step0Labels permutation32 permutation3
    _ = mixedMoment B node1347 node1347Labels := by rfl

def raw23378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23378step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23378step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23378step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw23378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23378 raw23378Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw23378 raw23378Labels = mixedMoment B raw23378step0 raw23378step0Labels := by
      have hz : ∀ j, raw23378 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23378step0 = (fun i j => raw23378 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23378step0 raw23378; decide +kernel
      have hl : raw23378step0Labels = raw23378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23378 raw23378Labels permutation346 hz
    mixedMoment B raw23378step0 raw23378step0Labels = mixedMoment B raw23378step1 raw23378step1Labels := by
      have hz : ∀ j, raw23378step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23378step1 = (fun i j => raw23378step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23378step1 raw23378step0; decide +kernel
      have hl : raw23378step1Labels = raw23378step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23378step0 raw23378step0Labels permutation56 hz
    mixedMoment B raw23378step1 raw23378step1Labels = mixedMoment B raw23378step2 raw23378step2Labels := by
      have ha : raw23378step2 = (fun i j => raw23378step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23378step2 raw23378step1; decide +kernel
      have hl : raw23378step2Labels = raw23378step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23378step1 raw23378step1Labels permutation10 permutation3
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw23379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23379step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23379 raw23379Labels = mixedMoment B node1451 node1451Labels := by
  calc
    mixedMoment B raw23379 raw23379Labels = mixedMoment B raw23379step0 raw23379step0Labels := by
      have hz : ∀ j, raw23379 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23379step0 = (fun i j => raw23379 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23379step0 raw23379; decide +kernel
      have hl : raw23379step0Labels = raw23379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23379 raw23379Labels permutation346 hz
    mixedMoment B raw23379step0 raw23379step0Labels = mixedMoment B raw23379step1 raw23379step1Labels := by
      have hz : ∀ j, raw23379step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23379step1 = (fun i j => raw23379step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23379step1 raw23379step0; decide +kernel
      have hl : raw23379step1Labels = raw23379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23379step0 raw23379step0Labels permutation56 hz
    mixedMoment B raw23379step1 raw23379step1Labels = mixedMoment B raw23379step2 raw23379step2Labels := by
      have ha : raw23379step2 = (fun i j => raw23379step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23379step2 raw23379step1; decide +kernel
      have hl : raw23379step2Labels = raw23379step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23379step1 raw23379step1Labels permutation9 permutation3
    _ = mixedMoment B node1451 node1451Labels := by rfl

def raw23380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23380step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23380step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, 0, -3], ![2, -2, 0]]
def raw23380step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23380step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def raw23380step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23380 raw23380Labels = mixedMoment B node655 node655Labels := by
  calc
    mixedMoment B raw23380 raw23380Labels = mixedMoment B raw23380step0 raw23380step0Labels := by
      have hz : ∀ j, raw23380 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23380step0 = (fun i j => raw23380 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23380step0 raw23380; decide +kernel
      have hl : raw23380step0Labels = raw23380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23380 raw23380Labels permutation434 hz
    mixedMoment B raw23380step0 raw23380step0Labels = mixedMoment B raw23380step1 raw23380step1Labels := by
      have hz : ∀ j, raw23380step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23380step1 = (fun i j => raw23380step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23380step1 raw23380step0; decide +kernel
      have hl : raw23380step1Labels = raw23380step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23380step0 raw23380step0Labels permutation80 hz
    mixedMoment B raw23380step1 raw23380step1Labels = mixedMoment B raw23380step2 raw23380step2Labels := by
      have hz : ∀ j, raw23380step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23380step2 = (fun i j => raw23380step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23380step2 raw23380step1; decide +kernel
      have hl : raw23380step2Labels = raw23380step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23380step1 raw23380step1Labels permutation14 hz
    mixedMoment B raw23380step2 raw23380step2Labels = mixedMoment B raw23380step3 raw23380step3Labels := by
      have ha : raw23380step3 = (fun i j => raw23380step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23380step3 raw23380step2; decide +kernel
      have hl : raw23380step3Labels = raw23380step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23380step2 raw23380step2Labels permutation3 permutation3
    _ = mixedMoment B node655 node655Labels := by rfl

def raw23381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23381step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23381step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23381step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw23381step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23381 raw23381Labels = mixedMoment B node1349 node1349Labels := by
  calc
    mixedMoment B raw23381 raw23381Labels = mixedMoment B raw23381step0 raw23381step0Labels := by
      have hz : ∀ j, raw23381 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23381step0 = (fun i j => raw23381 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23381step0 raw23381; decide +kernel
      have hl : raw23381step0Labels = raw23381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23381 raw23381Labels permutation434 hz
    mixedMoment B raw23381step0 raw23381step0Labels = mixedMoment B raw23381step1 raw23381step1Labels := by
      have hz : ∀ j, raw23381step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23381step1 = (fun i j => raw23381step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23381step1 raw23381step0; decide +kernel
      have hl : raw23381step1Labels = raw23381step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23381step0 raw23381step0Labels permutation80 hz
    mixedMoment B raw23381step1 raw23381step1Labels = mixedMoment B raw23381step2 raw23381step2Labels := by
      have ha : raw23381step2 = (fun i j => raw23381step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23381step2 raw23381step1; decide +kernel
      have hl : raw23381step2Labels = raw23381step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23381step1 raw23381step1Labels permutation9 permutation3
    _ = mixedMoment B node1349 node1349Labels := by rfl

def raw23382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23382step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23382step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw23382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23382 raw23382Labels = mixedMoment B node1349 node1349Labels := by
  calc
    mixedMoment B raw23382 raw23382Labels = mixedMoment B raw23382step0 raw23382step0Labels := by
      have hz : ∀ j, raw23382 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23382step0 = (fun i j => raw23382 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23382step0 raw23382; decide +kernel
      have hl : raw23382step0Labels = raw23382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23382 raw23382Labels permutation434 hz
    mixedMoment B raw23382step0 raw23382step0Labels = mixedMoment B raw23382step1 raw23382step1Labels := by
      have hz : ∀ j, raw23382step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23382step1 = (fun i j => raw23382step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23382step1 raw23382step0; decide +kernel
      have hl : raw23382step1Labels = raw23382step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23382step0 raw23382step0Labels permutation56 hz
    mixedMoment B raw23382step1 raw23382step1Labels = mixedMoment B raw23382step2 raw23382step2Labels := by
      have ha : raw23382step2 = (fun i j => raw23382step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23382step2 raw23382step1; decide +kernel
      have hl : raw23382step2Labels = raw23382step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23382step1 raw23382step1Labels permutation9 permutation3
    _ = mixedMoment B node1349 node1349Labels := by rfl

def raw23383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23383step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23383step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def raw23383step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23383 raw23383Labels = mixedMoment B node1349 node1349Labels := by
  calc
    mixedMoment B raw23383 raw23383Labels = mixedMoment B raw23383step0 raw23383step0Labels := by
      have hz : ∀ j, raw23383 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23383step0 = (fun i j => raw23383 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23383step0 raw23383; decide +kernel
      have hl : raw23383step0Labels = raw23383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23383 raw23383Labels permutation346 hz
    mixedMoment B raw23383step0 raw23383step0Labels = mixedMoment B raw23383step1 raw23383step1Labels := by
      have hz : ∀ j, raw23383step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23383step1 = (fun i j => raw23383step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23383step1 raw23383step0; decide +kernel
      have hl : raw23383step1Labels = raw23383step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23383step0 raw23383step0Labels permutation56 hz
    mixedMoment B raw23383step1 raw23383step1Labels = mixedMoment B raw23383step2 raw23383step2Labels := by
      have ha : raw23383step2 = (fun i j => raw23383step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23383step2 raw23383step1; decide +kernel
      have hl : raw23383step2Labels = raw23383step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23383step1 raw23383step1Labels permutation9 permutation3
    _ = mixedMoment B node1349 node1349Labels := by rfl

def raw23384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23384step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23384step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, 0, -3], ![1, -1, 0]]
def raw23384step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23384step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def raw23384step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23384 raw23384Labels = mixedMoment B node1452 node1452Labels := by
  calc
    mixedMoment B raw23384 raw23384Labels = mixedMoment B raw23384step0 raw23384step0Labels := by
      have hz : ∀ j, raw23384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23384step0 = (fun i j => raw23384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23384step0 raw23384; decide +kernel
      have hl : raw23384step0Labels = raw23384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23384 raw23384Labels permutation434 hz
    mixedMoment B raw23384step0 raw23384step0Labels = mixedMoment B raw23384step1 raw23384step1Labels := by
      have hz : ∀ j, raw23384step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23384step1 = (fun i j => raw23384step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23384step1 raw23384step0; decide +kernel
      have hl : raw23384step1Labels = raw23384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23384step0 raw23384step0Labels permutation80 hz
    mixedMoment B raw23384step1 raw23384step1Labels = mixedMoment B raw23384step2 raw23384step2Labels := by
      have hz : ∀ j, raw23384step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23384step2 = (fun i j => raw23384step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23384step2 raw23384step1; decide +kernel
      have hl : raw23384step2Labels = raw23384step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23384step1 raw23384step1Labels permutation14 hz
    mixedMoment B raw23384step2 raw23384step2Labels = mixedMoment B raw23384step3 raw23384step3Labels := by
      have ha : raw23384step3 = (fun i j => raw23384step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23384step3 raw23384step2; decide +kernel
      have hl : raw23384step3Labels = raw23384step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23384step2 raw23384step2Labels permutation3 permutation3
    _ = mixedMoment B node1452 node1452Labels := by rfl

def raw23385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23385step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23385step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw23385step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23385step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw23385step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23385 raw23385Labels = mixedMoment B node654 node654Labels := by
  calc
    mixedMoment B raw23385 raw23385Labels = mixedMoment B raw23385step0 raw23385step0Labels := by
      have hz : ∀ j, raw23385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23385step0 = (fun i j => raw23385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23385step0 raw23385; decide +kernel
      have hl : raw23385step0Labels = raw23385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23385 raw23385Labels permutation434 hz
    mixedMoment B raw23385step0 raw23385step0Labels = mixedMoment B raw23385step1 raw23385step1Labels := by
      have hz : ∀ j, raw23385step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23385step1 = (fun i j => raw23385step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23385step1 raw23385step0; decide +kernel
      have hl : raw23385step1Labels = raw23385step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23385step0 raw23385step0Labels permutation80 hz
    mixedMoment B raw23385step1 raw23385step1Labels = mixedMoment B raw23385step2 raw23385step2Labels := by
      have hz : ∀ j, raw23385step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23385step2 = (fun i j => raw23385step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23385step2 raw23385step1; decide +kernel
      have hl : raw23385step2Labels = raw23385step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23385step1 raw23385step1Labels permutation14 hz
    mixedMoment B raw23385step2 raw23385step2Labels = mixedMoment B raw23385step3 raw23385step3Labels := by
      have ha : raw23385step3 = (fun i j => raw23385step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23385step3 raw23385step2; decide +kernel
      have hl : raw23385step3Labels = raw23385step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23385step2 raw23385step2Labels permutation2 permutation3
    _ = mixedMoment B node654 node654Labels := by rfl

def raw23386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23386step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw23386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23386 raw23386Labels = mixedMoment B node1348 node1348Labels := by
  calc
    mixedMoment B raw23386 raw23386Labels = mixedMoment B raw23386step0 raw23386step0Labels := by
      have hz : ∀ j, raw23386 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23386step0 = (fun i j => raw23386 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23386step0 raw23386; decide +kernel
      have hl : raw23386step0Labels = raw23386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23386 raw23386Labels permutation434 hz
    mixedMoment B raw23386step0 raw23386step0Labels = mixedMoment B raw23386step1 raw23386step1Labels := by
      have hz : ∀ j, raw23386step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23386step1 = (fun i j => raw23386step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23386step1 raw23386step0; decide +kernel
      have hl : raw23386step1Labels = raw23386step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23386step0 raw23386step0Labels permutation80 hz
    mixedMoment B raw23386step1 raw23386step1Labels = mixedMoment B raw23386step2 raw23386step2Labels := by
      have ha : raw23386step2 = (fun i j => raw23386step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23386step2 raw23386step1; decide +kernel
      have hl : raw23386step2Labels = raw23386step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23386step1 raw23386step1Labels permutation8 permutation3
    _ = mixedMoment B node1348 node1348Labels := by rfl

def raw23387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23387step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw23387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23387 raw23387Labels = mixedMoment B node1348 node1348Labels := by
  calc
    mixedMoment B raw23387 raw23387Labels = mixedMoment B raw23387step0 raw23387step0Labels := by
      have hz : ∀ j, raw23387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23387step0 = (fun i j => raw23387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23387step0 raw23387; decide +kernel
      have hl : raw23387step0Labels = raw23387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23387 raw23387Labels permutation434 hz
    mixedMoment B raw23387step0 raw23387step0Labels = mixedMoment B raw23387step1 raw23387step1Labels := by
      have hz : ∀ j, raw23387step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23387step1 = (fun i j => raw23387step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23387step1 raw23387step0; decide +kernel
      have hl : raw23387step1Labels = raw23387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23387step0 raw23387step0Labels permutation56 hz
    mixedMoment B raw23387step1 raw23387step1Labels = mixedMoment B raw23387step2 raw23387step2Labels := by
      have ha : raw23387step2 = (fun i j => raw23387step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23387step2 raw23387step1; decide +kernel
      have hl : raw23387step2Labels = raw23387step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23387step1 raw23387step1Labels permutation8 permutation3
    _ = mixedMoment B node1348 node1348Labels := by rfl

def raw23388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23388step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw23388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23388 raw23388Labels = mixedMoment B node1348 node1348Labels := by
  calc
    mixedMoment B raw23388 raw23388Labels = mixedMoment B raw23388step0 raw23388step0Labels := by
      have hz : ∀ j, raw23388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23388step0 = (fun i j => raw23388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23388step0 raw23388; decide +kernel
      have hl : raw23388step0Labels = raw23388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23388 raw23388Labels permutation346 hz
    mixedMoment B raw23388step0 raw23388step0Labels = mixedMoment B raw23388step1 raw23388step1Labels := by
      have hz : ∀ j, raw23388step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23388step1 = (fun i j => raw23388step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23388step1 raw23388step0; decide +kernel
      have hl : raw23388step1Labels = raw23388step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23388step0 raw23388step0Labels permutation56 hz
    mixedMoment B raw23388step1 raw23388step1Labels = mixedMoment B raw23388step2 raw23388step2Labels := by
      have ha : raw23388step2 = (fun i j => raw23388step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23388step2 raw23388step1; decide +kernel
      have hl : raw23388step2Labels = raw23388step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23388step1 raw23388step1Labels permutation8 permutation3
    _ = mixedMoment B node1348 node1348Labels := by rfl

def raw23389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23389Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23389step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23389step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw23389step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23389step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23389step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23389step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23389step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23389 raw23389Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw23389 raw23389Labels = mixedMoment B raw23389step0 raw23389step0Labels := by
      have hz : ∀ j, raw23389 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23389step0 = (fun i j => raw23389 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23389step0 raw23389; decide +kernel
      have hl : raw23389step0Labels = raw23389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23389 raw23389Labels permutation434 hz
    mixedMoment B raw23389step0 raw23389step0Labels = mixedMoment B raw23389step1 raw23389step1Labels := by
      have hz : ∀ j, raw23389step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23389step1 = (fun i j => raw23389step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23389step1 raw23389step0; decide +kernel
      have hl : raw23389step1Labels = raw23389step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23389step0 raw23389step0Labels permutation80 hz
    mixedMoment B raw23389step1 raw23389step1Labels = mixedMoment B raw23389step2 raw23389step2Labels := by
      have ha : raw23389step2 = (fun i j => raw23389step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23389step2 raw23389step1; decide +kernel
      have hl : raw23389step2Labels = raw23389step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23389step1 raw23389step1Labels permutation9 permutation7
    mixedMoment B raw23389step2 raw23389step2Labels = mixedMoment B raw23389step3 raw23389step3Labels := by
      have ha : raw23389step3 = -raw23389step2 := by apply Matrix.ext; change ∀ i j, raw23389step3 i j = -(raw23389step2 i j); unfold raw23389step3 raw23389step2; decide +kernel
      have hl : raw23389step3Labels = raw23389step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23389step3 raw23389step3Labels = mixedMoment B raw23389step4 raw23389step4Labels := by
      have ha : raw23389step4 = raw23389step3 := by apply Matrix.ext; unfold raw23389step4 raw23389step3; decide +kernel
      have hl : raw23389step3Labels = labelEmbedding1 ∘ raw23389step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23389step3 raw23389step3Labels raw23389step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw23390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23390Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23390step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23390step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw23390step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23390step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23390step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23390step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23390step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23390 raw23390Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw23390 raw23390Labels = mixedMoment B raw23390step0 raw23390step0Labels := by
      have hz : ∀ j, raw23390 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23390step0 = (fun i j => raw23390 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23390step0 raw23390; decide +kernel
      have hl : raw23390step0Labels = raw23390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23390 raw23390Labels permutation434 hz
    mixedMoment B raw23390step0 raw23390step0Labels = mixedMoment B raw23390step1 raw23390step1Labels := by
      have hz : ∀ j, raw23390step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23390step1 = (fun i j => raw23390step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23390step1 raw23390step0; decide +kernel
      have hl : raw23390step1Labels = raw23390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23390step0 raw23390step0Labels permutation56 hz
    mixedMoment B raw23390step1 raw23390step1Labels = mixedMoment B raw23390step2 raw23390step2Labels := by
      have ha : raw23390step2 = (fun i j => raw23390step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23390step2 raw23390step1; decide +kernel
      have hl : raw23390step2Labels = raw23390step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23390step1 raw23390step1Labels permutation9 permutation7
    mixedMoment B raw23390step2 raw23390step2Labels = mixedMoment B raw23390step3 raw23390step3Labels := by
      have ha : raw23390step3 = -raw23390step2 := by apply Matrix.ext; change ∀ i j, raw23390step3 i j = -(raw23390step2 i j); unfold raw23390step3 raw23390step2; decide +kernel
      have hl : raw23390step3Labels = raw23390step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23390step3 raw23390step3Labels = mixedMoment B raw23390step4 raw23390step4Labels := by
      have ha : raw23390step4 = raw23390step3 := by apply Matrix.ext; unfold raw23390step4 raw23390step3; decide +kernel
      have hl : raw23390step3Labels = labelEmbedding1 ∘ raw23390step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23390step3 raw23390step3Labels raw23390step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw23391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23391Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23391step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23391step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23391step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw23391step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23391step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23391step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23391step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw23391step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23391 raw23391Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw23391 raw23391Labels = mixedMoment B raw23391step0 raw23391step0Labels := by
      have hz : ∀ j, raw23391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23391step0 = (fun i j => raw23391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23391step0 raw23391; decide +kernel
      have hl : raw23391step0Labels = raw23391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23391 raw23391Labels permutation346 hz
    mixedMoment B raw23391step0 raw23391step0Labels = mixedMoment B raw23391step1 raw23391step1Labels := by
      have hz : ∀ j, raw23391step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23391step1 = (fun i j => raw23391step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23391step1 raw23391step0; decide +kernel
      have hl : raw23391step1Labels = raw23391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23391step0 raw23391step0Labels permutation56 hz
    mixedMoment B raw23391step1 raw23391step1Labels = mixedMoment B raw23391step2 raw23391step2Labels := by
      have ha : raw23391step2 = (fun i j => raw23391step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23391step2 raw23391step1; decide +kernel
      have hl : raw23391step2Labels = raw23391step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23391step1 raw23391step1Labels permutation9 permutation7
    mixedMoment B raw23391step2 raw23391step2Labels = mixedMoment B raw23391step3 raw23391step3Labels := by
      have ha : raw23391step3 = -raw23391step2 := by apply Matrix.ext; change ∀ i j, raw23391step3 i j = -(raw23391step2 i j); unfold raw23391step3 raw23391step2; decide +kernel
      have hl : raw23391step3Labels = raw23391step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23391step3 raw23391step3Labels = mixedMoment B raw23391step4 raw23391step4Labels := by
      have ha : raw23391step4 = raw23391step3 := by apply Matrix.ext; unfold raw23391step4 raw23391step3; decide +kernel
      have hl : raw23391step3Labels = labelEmbedding1 ∘ raw23391step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23391step3 raw23391step3Labels raw23391step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw23392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23392step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23392step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23392step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw23392step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23392step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw23392step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23392step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw23392step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23392step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw23392step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23392 raw23392Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw23392 raw23392Labels = mixedMoment B raw23392step0 raw23392step0Labels := by
      have hz : ∀ j, raw23392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23392step0 = (fun i j => raw23392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23392step0 raw23392; decide +kernel
      have hl : raw23392step0Labels = raw23392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23392 raw23392Labels permutation434 hz
    mixedMoment B raw23392step0 raw23392step0Labels = mixedMoment B raw23392step1 raw23392step1Labels := by
      have hz : ∀ j, raw23392step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23392step1 = (fun i j => raw23392step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23392step1 raw23392step0; decide +kernel
      have hl : raw23392step1Labels = raw23392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23392step0 raw23392step0Labels permutation80 hz
    mixedMoment B raw23392step1 raw23392step1Labels = mixedMoment B raw23392step2 raw23392step2Labels := by
      have hz : ∀ j, raw23392step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23392step2 = (fun i j => raw23392step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23392step2 raw23392step1; decide +kernel
      have hl : raw23392step2Labels = raw23392step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23392step1 raw23392step1Labels permutation14 hz
    mixedMoment B raw23392step2 raw23392step2Labels = mixedMoment B raw23392step3 raw23392step3Labels := by
      have ha : raw23392step3 = (fun i j => raw23392step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23392step3 raw23392step2; decide +kernel
      have hl : raw23392step3Labels = raw23392step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23392step2 raw23392step2Labels permutation3 permutation7
    mixedMoment B raw23392step3 raw23392step3Labels = mixedMoment B raw23392step4 raw23392step4Labels := by
      have ha : raw23392step4 = -raw23392step3 := by apply Matrix.ext; change ∀ i j, raw23392step4 i j = -(raw23392step3 i j); unfold raw23392step4 raw23392step3; decide +kernel
      have hl : raw23392step4Labels = raw23392step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23392step4 raw23392step4Labels = mixedMoment B raw23392step5 raw23392step5Labels := by
      have ha : raw23392step5 = raw23392step4 := by apply Matrix.ext; unfold raw23392step5 raw23392step4; decide +kernel
      have hl : raw23392step4Labels = labelEmbedding1 ∘ raw23392step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23392step4 raw23392step4Labels raw23392step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw23393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23393Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23393step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23393step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23393step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![2, 1, -3], ![1, -1, 0]]
def raw23393step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23393step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw23393step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23393step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw23393step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23393step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw23393step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23393 raw23393Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw23393 raw23393Labels = mixedMoment B raw23393step0 raw23393step0Labels := by
      have hz : ∀ j, raw23393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23393step0 = (fun i j => raw23393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23393step0 raw23393; decide +kernel
      have hl : raw23393step0Labels = raw23393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23393 raw23393Labels permutation434 hz
    mixedMoment B raw23393step0 raw23393step0Labels = mixedMoment B raw23393step1 raw23393step1Labels := by
      have hz : ∀ j, raw23393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23393step1 = (fun i j => raw23393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23393step1 raw23393step0; decide +kernel
      have hl : raw23393step1Labels = raw23393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23393step0 raw23393step0Labels permutation80 hz
    mixedMoment B raw23393step1 raw23393step1Labels = mixedMoment B raw23393step2 raw23393step2Labels := by
      have hz : ∀ j, raw23393step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23393step2 = (fun i j => raw23393step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23393step2 raw23393step1; decide +kernel
      have hl : raw23393step2Labels = raw23393step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23393step1 raw23393step1Labels permutation14 hz
    mixedMoment B raw23393step2 raw23393step2Labels = mixedMoment B raw23393step3 raw23393step3Labels := by
      have ha : raw23393step3 = (fun i j => raw23393step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23393step3 raw23393step2; decide +kernel
      have hl : raw23393step3Labels = raw23393step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23393step2 raw23393step2Labels permutation3 permutation7
    mixedMoment B raw23393step3 raw23393step3Labels = mixedMoment B raw23393step4 raw23393step4Labels := by
      have ha : raw23393step4 = -raw23393step3 := by apply Matrix.ext; change ∀ i j, raw23393step4 i j = -(raw23393step3 i j); unfold raw23393step4 raw23393step3; decide +kernel
      have hl : raw23393step4Labels = raw23393step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23393step4 raw23393step4Labels = mixedMoment B raw23393step5 raw23393step5Labels := by
      have ha : raw23393step5 = raw23393step4 := by apply Matrix.ext; unfold raw23393step5 raw23393step4; decide +kernel
      have hl : raw23393step4Labels = labelEmbedding1 ∘ raw23393step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23393step4 raw23393step4Labels raw23393step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2268 node2268Labels := by rfl

def raw23394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23394Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23394step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23394step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23394step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23394step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23394step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23394step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23394step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23394 raw23394Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw23394 raw23394Labels = mixedMoment B raw23394step0 raw23394step0Labels := by
      have hz : ∀ j, raw23394 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23394step0 = (fun i j => raw23394 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23394step0 raw23394; decide +kernel
      have hl : raw23394step0Labels = raw23394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23394 raw23394Labels permutation434 hz
    mixedMoment B raw23394step0 raw23394step0Labels = mixedMoment B raw23394step1 raw23394step1Labels := by
      have hz : ∀ j, raw23394step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23394step1 = (fun i j => raw23394step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23394step1 raw23394step0; decide +kernel
      have hl : raw23394step1Labels = raw23394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23394step0 raw23394step0Labels permutation80 hz
    mixedMoment B raw23394step1 raw23394step1Labels = mixedMoment B raw23394step2 raw23394step2Labels := by
      have ha : raw23394step2 = (fun i j => raw23394step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23394step2 raw23394step1; decide +kernel
      have hl : raw23394step2Labels = raw23394step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23394step1 raw23394step1Labels permutation9 permutation7
    mixedMoment B raw23394step2 raw23394step2Labels = mixedMoment B raw23394step3 raw23394step3Labels := by
      have ha : raw23394step3 = -raw23394step2 := by apply Matrix.ext; change ∀ i j, raw23394step3 i j = -(raw23394step2 i j); unfold raw23394step3 raw23394step2; decide +kernel
      have hl : raw23394step3Labels = raw23394step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23394step3 raw23394step3Labels = mixedMoment B raw23394step4 raw23394step4Labels := by
      have ha : raw23394step4 = raw23394step3 := by apply Matrix.ext; unfold raw23394step4 raw23394step3; decide +kernel
      have hl : raw23394step3Labels = labelEmbedding1 ∘ raw23394step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23394step3 raw23394step3Labels raw23394step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

def raw23395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23395Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23395step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23395step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23395step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23395step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23395step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23395 raw23395Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23395 raw23395Labels = mixedMoment B raw23395step0 raw23395step0Labels := by
      have hz : ∀ j, raw23395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23395step0 = (fun i j => raw23395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23395step0 raw23395; decide +kernel
      have hl : raw23395step0Labels = raw23395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23395 raw23395Labels permutation434 hz
    mixedMoment B raw23395step0 raw23395step0Labels = mixedMoment B raw23395step1 raw23395step1Labels := by
      have ha : raw23395step1 = (fun i j => raw23395step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23395step1 raw23395step0; decide +kernel
      have hl : raw23395step1Labels = raw23395step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23395step0 raw23395step0Labels permutation39 permutation7
    mixedMoment B raw23395step1 raw23395step1Labels = mixedMoment B raw23395step2 raw23395step2Labels := by
      have ha : raw23395step2 = -raw23395step1 := by apply Matrix.ext; change ∀ i j, raw23395step2 i j = -(raw23395step1 i j); unfold raw23395step2 raw23395step1; decide +kernel
      have hl : raw23395step2Labels = raw23395step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23395step2 raw23395step2Labels = mixedMoment B raw23395step3 raw23395step3Labels := by
      have ha : raw23395step3 = raw23395step2 := by apply Matrix.ext; unfold raw23395step3 raw23395step2; decide +kernel
      have hl : raw23395step2Labels = labelEmbedding1 ∘ raw23395step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23395step2 raw23395step2Labels raw23395step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

def raw23396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23396Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23396step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23396step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23396step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23396step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23396step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23396 raw23396Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23396 raw23396Labels = mixedMoment B raw23396step0 raw23396step0Labels := by
      have hz : ∀ j, raw23396 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23396step0 = (fun i j => raw23396 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23396step0 raw23396; decide +kernel
      have hl : raw23396step0Labels = raw23396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23396 raw23396Labels permutation346 hz
    mixedMoment B raw23396step0 raw23396step0Labels = mixedMoment B raw23396step1 raw23396step1Labels := by
      have ha : raw23396step1 = (fun i j => raw23396step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23396step1 raw23396step0; decide +kernel
      have hl : raw23396step1Labels = raw23396step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23396step0 raw23396step0Labels permutation39 permutation7
    mixedMoment B raw23396step1 raw23396step1Labels = mixedMoment B raw23396step2 raw23396step2Labels := by
      have ha : raw23396step2 = -raw23396step1 := by apply Matrix.ext; change ∀ i j, raw23396step2 i j = -(raw23396step1 i j); unfold raw23396step2 raw23396step1; decide +kernel
      have hl : raw23396step2Labels = raw23396step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23396step2 raw23396step2Labels = mixedMoment B raw23396step3 raw23396step3Labels := by
      have ha : raw23396step3 = raw23396step2 := by apply Matrix.ext; unfold raw23396step3 raw23396step2; decide +kernel
      have hl : raw23396step2Labels = labelEmbedding1 ∘ raw23396step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23396step2 raw23396step2Labels raw23396step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

def raw23397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23397Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23397step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23397step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw23397step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23397step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23397step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23397step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23397step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23397 raw23397Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw23397 raw23397Labels = mixedMoment B raw23397step0 raw23397step0Labels := by
      have hz : ∀ j, raw23397 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23397step0 = (fun i j => raw23397 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23397step0 raw23397; decide +kernel
      have hl : raw23397step0Labels = raw23397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23397 raw23397Labels permutation434 hz
    mixedMoment B raw23397step0 raw23397step0Labels = mixedMoment B raw23397step1 raw23397step1Labels := by
      have hz : ∀ j, raw23397step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23397step1 = (fun i j => raw23397step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23397step1 raw23397step0; decide +kernel
      have hl : raw23397step1Labels = raw23397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23397step0 raw23397step0Labels permutation80 hz
    mixedMoment B raw23397step1 raw23397step1Labels = mixedMoment B raw23397step2 raw23397step2Labels := by
      have ha : raw23397step2 = (fun i j => raw23397step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23397step2 raw23397step1; decide +kernel
      have hl : raw23397step2Labels = raw23397step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23397step1 raw23397step1Labels permutation9 permutation7
    mixedMoment B raw23397step2 raw23397step2Labels = mixedMoment B raw23397step3 raw23397step3Labels := by
      have ha : raw23397step3 = -raw23397step2 := by apply Matrix.ext; change ∀ i j, raw23397step3 i j = -(raw23397step2 i j); unfold raw23397step3 raw23397step2; decide +kernel
      have hl : raw23397step3Labels = raw23397step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23397step3 raw23397step3Labels = mixedMoment B raw23397step4 raw23397step4Labels := by
      have ha : raw23397step4 = raw23397step3 := by apply Matrix.ext; unfold raw23397step4 raw23397step3; decide +kernel
      have hl : raw23397step3Labels = labelEmbedding1 ∘ raw23397step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23397step3 raw23397step3Labels raw23397step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw23398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23398Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23398step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23398step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23398step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23398step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23398step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23398step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23398step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23398step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23398 raw23398Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw23398 raw23398Labels = mixedMoment B raw23398step0 raw23398step0Labels := by
      have hz : ∀ j, raw23398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23398step0 = (fun i j => raw23398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23398step0 raw23398; decide +kernel
      have hl : raw23398step0Labels = raw23398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23398 raw23398Labels permutation434 hz
    mixedMoment B raw23398step0 raw23398step0Labels = mixedMoment B raw23398step1 raw23398step1Labels := by
      have hz : ∀ j, raw23398step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23398step1 = (fun i j => raw23398step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23398step1 raw23398step0; decide +kernel
      have hl : raw23398step1Labels = raw23398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23398step0 raw23398step0Labels permutation80 hz
    mixedMoment B raw23398step1 raw23398step1Labels = mixedMoment B raw23398step2 raw23398step2Labels := by
      have ha : raw23398step2 = (fun i j => raw23398step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23398step2 raw23398step1; decide +kernel
      have hl : raw23398step2Labels = raw23398step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23398step1 raw23398step1Labels permutation9 permutation7
    mixedMoment B raw23398step2 raw23398step2Labels = mixedMoment B raw23398step3 raw23398step3Labels := by
      have ha : raw23398step3 = -raw23398step2 := by apply Matrix.ext; change ∀ i j, raw23398step3 i j = -(raw23398step2 i j); unfold raw23398step3 raw23398step2; decide +kernel
      have hl : raw23398step3Labels = raw23398step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23398step3 raw23398step3Labels = mixedMoment B raw23398step4 raw23398step4Labels := by
      have ha : raw23398step4 = raw23398step3 := by apply Matrix.ext; unfold raw23398step4 raw23398step3; decide +kernel
      have hl : raw23398step3Labels = labelEmbedding1 ∘ raw23398step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23398step3 raw23398step3Labels raw23398step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw23399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23399Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23399step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23399step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23399step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23399step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23399step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23399step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23399step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23399 raw23399Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw23399 raw23399Labels = mixedMoment B raw23399step0 raw23399step0Labels := by
      have hz : ∀ j, raw23399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23399step0 = (fun i j => raw23399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23399step0 raw23399; decide +kernel
      have hl : raw23399step0Labels = raw23399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23399 raw23399Labels permutation434 hz
    mixedMoment B raw23399step0 raw23399step0Labels = mixedMoment B raw23399step1 raw23399step1Labels := by
      have hz : ∀ j, raw23399step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23399step1 = (fun i j => raw23399step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23399step1 raw23399step0; decide +kernel
      have hl : raw23399step1Labels = raw23399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23399step0 raw23399step0Labels permutation56 hz
    mixedMoment B raw23399step1 raw23399step1Labels = mixedMoment B raw23399step2 raw23399step2Labels := by
      have ha : raw23399step2 = (fun i j => raw23399step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23399step2 raw23399step1; decide +kernel
      have hl : raw23399step2Labels = raw23399step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23399step1 raw23399step1Labels permutation9 permutation7
    mixedMoment B raw23399step2 raw23399step2Labels = mixedMoment B raw23399step3 raw23399step3Labels := by
      have ha : raw23399step3 = -raw23399step2 := by apply Matrix.ext; change ∀ i j, raw23399step3 i j = -(raw23399step2 i j); unfold raw23399step3 raw23399step2; decide +kernel
      have hl : raw23399step3Labels = raw23399step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23399step3 raw23399step3Labels = mixedMoment B raw23399step4 raw23399step4Labels := by
      have ha : raw23399step4 = raw23399step3 := by apply Matrix.ext; unfold raw23399step4 raw23399step3; decide +kernel
      have hl : raw23399step3Labels = labelEmbedding1 ∘ raw23399step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23399step3 raw23399step3Labels raw23399step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

def raw23400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23400Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23400step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23400step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23400step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23400step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23400 raw23400Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23400 raw23400Labels = mixedMoment B raw23400step0 raw23400step0Labels := by
      have hz : ∀ j, raw23400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23400step0 = (fun i j => raw23400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23400step0 raw23400; decide +kernel
      have hl : raw23400step0Labels = raw23400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23400 raw23400Labels permutation434 hz
    mixedMoment B raw23400step0 raw23400step0Labels = mixedMoment B raw23400step1 raw23400step1Labels := by
      have ha : raw23400step1 = (fun i j => raw23400step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23400step1 raw23400step0; decide +kernel
      have hl : raw23400step1Labels = raw23400step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23400step0 raw23400step0Labels permutation33 permutation7
    mixedMoment B raw23400step1 raw23400step1Labels = mixedMoment B raw23400step2 raw23400step2Labels := by
      have ha : raw23400step2 = -raw23400step1 := by apply Matrix.ext; change ∀ i j, raw23400step2 i j = -(raw23400step1 i j); unfold raw23400step2 raw23400step1; decide +kernel
      have hl : raw23400step2Labels = raw23400step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23400step2 raw23400step2Labels = mixedMoment B raw23400step3 raw23400step3Labels := by
      have ha : raw23400step3 = raw23400step2 := by apply Matrix.ext; unfold raw23400step3 raw23400step2; decide +kernel
      have hl : raw23400step2Labels = labelEmbedding1 ∘ raw23400step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23400step2 raw23400step2Labels raw23400step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

def raw23401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23401Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23401step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23401step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23401step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23401step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23401 raw23401Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23401 raw23401Labels = mixedMoment B raw23401step0 raw23401step0Labels := by
      have hz : ∀ j, raw23401 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23401step0 = (fun i j => raw23401 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23401step0 raw23401; decide +kernel
      have hl : raw23401step0Labels = raw23401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23401 raw23401Labels permutation265 hz
    mixedMoment B raw23401step0 raw23401step0Labels = mixedMoment B raw23401step1 raw23401step1Labels := by
      have ha : raw23401step1 = (fun i j => raw23401step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23401step1 raw23401step0; decide +kernel
      have hl : raw23401step1Labels = raw23401step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23401step0 raw23401step0Labels permutation39 permutation7
    mixedMoment B raw23401step1 raw23401step1Labels = mixedMoment B raw23401step2 raw23401step2Labels := by
      have ha : raw23401step2 = -raw23401step1 := by apply Matrix.ext; change ∀ i j, raw23401step2 i j = -(raw23401step1 i j); unfold raw23401step2 raw23401step1; decide +kernel
      have hl : raw23401step2Labels = raw23401step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23401step2 raw23401step2Labels = mixedMoment B raw23401step3 raw23401step3Labels := by
      have ha : raw23401step3 = raw23401step2 := by apply Matrix.ext; unfold raw23401step3 raw23401step2; decide +kernel
      have hl : raw23401step2Labels = labelEmbedding1 ∘ raw23401step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23401step2 raw23401step2Labels raw23401step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

def raw23402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23402step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23402step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23402step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw23402step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23402step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23402step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23402step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23402step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23402 raw23402Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw23402 raw23402Labels = mixedMoment B raw23402step0 raw23402step0Labels := by
      have hz : ∀ j, raw23402 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23402step0 = (fun i j => raw23402 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23402step0 raw23402; decide +kernel
      have hl : raw23402step0Labels = raw23402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23402 raw23402Labels permutation434 hz
    mixedMoment B raw23402step0 raw23402step0Labels = mixedMoment B raw23402step1 raw23402step1Labels := by
      have hz : ∀ j, raw23402step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23402step1 = (fun i j => raw23402step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23402step1 raw23402step0; decide +kernel
      have hl : raw23402step1Labels = raw23402step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23402step0 raw23402step0Labels permutation56 hz
    mixedMoment B raw23402step1 raw23402step1Labels = mixedMoment B raw23402step2 raw23402step2Labels := by
      have ha : raw23402step2 = (fun i j => raw23402step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23402step2 raw23402step1; decide +kernel
      have hl : raw23402step2Labels = raw23402step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23402step1 raw23402step1Labels permutation9 permutation7
    mixedMoment B raw23402step2 raw23402step2Labels = mixedMoment B raw23402step3 raw23402step3Labels := by
      have ha : raw23402step3 = -raw23402step2 := by apply Matrix.ext; change ∀ i j, raw23402step3 i j = -(raw23402step2 i j); unfold raw23402step3 raw23402step2; decide +kernel
      have hl : raw23402step3Labels = raw23402step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23402step3 raw23402step3Labels = mixedMoment B raw23402step4 raw23402step4Labels := by
      have ha : raw23402step4 = raw23402step3 := by apply Matrix.ext; unfold raw23402step4 raw23402step3; decide +kernel
      have hl : raw23402step3Labels = labelEmbedding1 ∘ raw23402step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23402step3 raw23402step3Labels raw23402step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw23403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23403step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23403step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23403step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23403step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23403step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23403step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23403step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23403step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23403 raw23403Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw23403 raw23403Labels = mixedMoment B raw23403step0 raw23403step0Labels := by
      have hz : ∀ j, raw23403 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23403step0 = (fun i j => raw23403 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23403step0 raw23403; decide +kernel
      have hl : raw23403step0Labels = raw23403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23403 raw23403Labels permutation434 hz
    mixedMoment B raw23403step0 raw23403step0Labels = mixedMoment B raw23403step1 raw23403step1Labels := by
      have hz : ∀ j, raw23403step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23403step1 = (fun i j => raw23403step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23403step1 raw23403step0; decide +kernel
      have hl : raw23403step1Labels = raw23403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23403step0 raw23403step0Labels permutation56 hz
    mixedMoment B raw23403step1 raw23403step1Labels = mixedMoment B raw23403step2 raw23403step2Labels := by
      have ha : raw23403step2 = (fun i j => raw23403step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23403step2 raw23403step1; decide +kernel
      have hl : raw23403step2Labels = raw23403step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23403step1 raw23403step1Labels permutation9 permutation7
    mixedMoment B raw23403step2 raw23403step2Labels = mixedMoment B raw23403step3 raw23403step3Labels := by
      have ha : raw23403step3 = -raw23403step2 := by apply Matrix.ext; change ∀ i j, raw23403step3 i j = -(raw23403step2 i j); unfold raw23403step3 raw23403step2; decide +kernel
      have hl : raw23403step3Labels = raw23403step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23403step3 raw23403step3Labels = mixedMoment B raw23403step4 raw23403step4Labels := by
      have ha : raw23403step4 = raw23403step3 := by apply Matrix.ext; unfold raw23403step4 raw23403step3; decide +kernel
      have hl : raw23403step3Labels = labelEmbedding1 ∘ raw23403step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23403step3 raw23403step3Labels raw23403step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw23404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23404step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23404step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23404step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23404step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23404step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23404 raw23404Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw23404 raw23404Labels = mixedMoment B raw23404step0 raw23404step0Labels := by
      have hz : ∀ j, raw23404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23404step0 = (fun i j => raw23404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23404step0 raw23404; decide +kernel
      have hl : raw23404step0Labels = raw23404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23404 raw23404Labels permutation346 hz
    mixedMoment B raw23404step0 raw23404step0Labels = mixedMoment B raw23404step1 raw23404step1Labels := by
      have hz : ∀ j, raw23404step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23404step1 = (fun i j => raw23404step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23404step1 raw23404step0; decide +kernel
      have hl : raw23404step1Labels = raw23404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23404step0 raw23404step0Labels permutation56 hz
    mixedMoment B raw23404step1 raw23404step1Labels = mixedMoment B raw23404step2 raw23404step2Labels := by
      have ha : raw23404step2 = (fun i j => raw23404step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23404step2 raw23404step1; decide +kernel
      have hl : raw23404step2Labels = raw23404step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23404step1 raw23404step1Labels permutation9 permutation7
    mixedMoment B raw23404step2 raw23404step2Labels = mixedMoment B raw23404step3 raw23404step3Labels := by
      have ha : raw23404step3 = -raw23404step2 := by apply Matrix.ext; change ∀ i j, raw23404step3 i j = -(raw23404step2 i j); unfold raw23404step3 raw23404step2; decide +kernel
      have hl : raw23404step3Labels = raw23404step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23404step3 raw23404step3Labels = mixedMoment B raw23404step4 raw23404step4Labels := by
      have ha : raw23404step4 = raw23404step3 := by apply Matrix.ext; unfold raw23404step4 raw23404step3; decide +kernel
      have hl : raw23404step3Labels = labelEmbedding1 ∘ raw23404step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23404step3 raw23404step3Labels raw23404step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

def raw23405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23405step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23405step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23405step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23405step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23405 raw23405Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23405 raw23405Labels = mixedMoment B raw23405step0 raw23405step0Labels := by
      have hz : ∀ j, raw23405 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23405step0 = (fun i j => raw23405 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23405step0 raw23405; decide +kernel
      have hl : raw23405step0Labels = raw23405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23405 raw23405Labels permutation346 hz
    mixedMoment B raw23405step0 raw23405step0Labels = mixedMoment B raw23405step1 raw23405step1Labels := by
      have ha : raw23405step1 = (fun i j => raw23405step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23405step1 raw23405step0; decide +kernel
      have hl : raw23405step1Labels = raw23405step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23405step0 raw23405step0Labels permutation33 permutation7
    mixedMoment B raw23405step1 raw23405step1Labels = mixedMoment B raw23405step2 raw23405step2Labels := by
      have ha : raw23405step2 = -raw23405step1 := by apply Matrix.ext; change ∀ i j, raw23405step2 i j = -(raw23405step1 i j); unfold raw23405step2 raw23405step1; decide +kernel
      have hl : raw23405step2Labels = raw23405step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23405step2 raw23405step2Labels = mixedMoment B raw23405step3 raw23405step3Labels := by
      have ha : raw23405step3 = raw23405step2 := by apply Matrix.ext; unfold raw23405step3 raw23405step2; decide +kernel
      have hl : raw23405step2Labels = labelEmbedding1 ∘ raw23405step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23405step2 raw23405step2Labels raw23405step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

def raw23406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw23406step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23406step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw23406step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23406 raw23406Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw23406 raw23406Labels = mixedMoment B raw23406step0 raw23406step0Labels := by
      have hz : ∀ j, raw23406 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23406step0 = (fun i j => raw23406 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23406step0 raw23406; decide +kernel
      have hl : raw23406step0Labels = raw23406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23406 raw23406Labels permutation265 hz
    mixedMoment B raw23406step0 raw23406step0Labels = mixedMoment B raw23406step1 raw23406step1Labels := by
      have ha : raw23406step1 = (fun i j => raw23406step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23406step1 raw23406step0; decide +kernel
      have hl : raw23406step1Labels = raw23406step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23406step0 raw23406step0Labels permutation33 permutation7
    mixedMoment B raw23406step1 raw23406step1Labels = mixedMoment B raw23406step2 raw23406step2Labels := by
      have ha : raw23406step2 = -raw23406step1 := by apply Matrix.ext; change ∀ i j, raw23406step2 i j = -(raw23406step1 i j); unfold raw23406step2 raw23406step1; decide +kernel
      have hl : raw23406step2Labels = raw23406step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23406step2 raw23406step2Labels = mixedMoment B raw23406step3 raw23406step3Labels := by
      have ha : raw23406step3 = raw23406step2 := by apply Matrix.ext; unfold raw23406step3 raw23406step2; decide +kernel
      have hl : raw23406step2Labels = labelEmbedding1 ∘ raw23406step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23406step2 raw23406step2Labels raw23406step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

def raw23407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23407step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw23407step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23407step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw23407step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23407step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23407step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23407step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw23407step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23407 raw23407Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw23407 raw23407Labels = mixedMoment B raw23407step0 raw23407step0Labels := by
      have hz : ∀ j, raw23407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23407step0 = (fun i j => raw23407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23407step0 raw23407; decide +kernel
      have hl : raw23407step0Labels = raw23407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23407 raw23407Labels permutation346 hz
    mixedMoment B raw23407step0 raw23407step0Labels = mixedMoment B raw23407step1 raw23407step1Labels := by
      have hz : ∀ j, raw23407step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23407step1 = (fun i j => raw23407step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23407step1 raw23407step0; decide +kernel
      have hl : raw23407step1Labels = raw23407step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23407step0 raw23407step0Labels permutation56 hz
    mixedMoment B raw23407step1 raw23407step1Labels = mixedMoment B raw23407step2 raw23407step2Labels := by
      have ha : raw23407step2 = (fun i j => raw23407step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23407step2 raw23407step1; decide +kernel
      have hl : raw23407step2Labels = raw23407step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23407step1 raw23407step1Labels permutation9 permutation7
    mixedMoment B raw23407step2 raw23407step2Labels = mixedMoment B raw23407step3 raw23407step3Labels := by
      have ha : raw23407step3 = -raw23407step2 := by apply Matrix.ext; change ∀ i j, raw23407step3 i j = -(raw23407step2 i j); unfold raw23407step3 raw23407step2; decide +kernel
      have hl : raw23407step3Labels = raw23407step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23407step3 raw23407step3Labels = mixedMoment B raw23407step4 raw23407step4Labels := by
      have ha : raw23407step4 = raw23407step3 := by apply Matrix.ext; unfold raw23407step4 raw23407step3; decide +kernel
      have hl : raw23407step3Labels = labelEmbedding1 ∘ raw23407step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23407step3 raw23407step3Labels raw23407step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw23408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23408step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw23408step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23408step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23408step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23408step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23408step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23408step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw23408step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23408 raw23408Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw23408 raw23408Labels = mixedMoment B raw23408step0 raw23408step0Labels := by
      have hz : ∀ j, raw23408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23408step0 = (fun i j => raw23408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23408step0 raw23408; decide +kernel
      have hl : raw23408step0Labels = raw23408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23408 raw23408Labels permutation346 hz
    mixedMoment B raw23408step0 raw23408step0Labels = mixedMoment B raw23408step1 raw23408step1Labels := by
      have hz : ∀ j, raw23408step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23408step1 = (fun i j => raw23408step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23408step1 raw23408step0; decide +kernel
      have hl : raw23408step1Labels = raw23408step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23408step0 raw23408step0Labels permutation56 hz
    mixedMoment B raw23408step1 raw23408step1Labels = mixedMoment B raw23408step2 raw23408step2Labels := by
      have ha : raw23408step2 = (fun i j => raw23408step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23408step2 raw23408step1; decide +kernel
      have hl : raw23408step2Labels = raw23408step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23408step1 raw23408step1Labels permutation9 permutation7
    mixedMoment B raw23408step2 raw23408step2Labels = mixedMoment B raw23408step3 raw23408step3Labels := by
      have ha : raw23408step3 = -raw23408step2 := by apply Matrix.ext; change ∀ i j, raw23408step3 i j = -(raw23408step2 i j); unfold raw23408step3 raw23408step2; decide +kernel
      have hl : raw23408step3Labels = raw23408step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23408step3 raw23408step3Labels = mixedMoment B raw23408step4 raw23408step4Labels := by
      have ha : raw23408step4 = raw23408step3 := by apply Matrix.ext; unfold raw23408step4 raw23408step3; decide +kernel
      have hl : raw23408step3Labels = labelEmbedding1 ∘ raw23408step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23408step3 raw23408step3Labels raw23408step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw23409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23409step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23409step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23409step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, 0, -3], ![2, -2, 0]]
def raw23409step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23409step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-3, 0, 3]]
def raw23409step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23409step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw23409step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23409step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw23409step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23409 raw23409Labels = mixedMoment B node1527 node1527Labels := by
  calc
    mixedMoment B raw23409 raw23409Labels = mixedMoment B raw23409step0 raw23409step0Labels := by
      have hz : ∀ j, raw23409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23409step0 = (fun i j => raw23409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23409step0 raw23409; decide +kernel
      have hl : raw23409step0Labels = raw23409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23409 raw23409Labels permutation434 hz
    mixedMoment B raw23409step0 raw23409step0Labels = mixedMoment B raw23409step1 raw23409step1Labels := by
      have hz : ∀ j, raw23409step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23409step1 = (fun i j => raw23409step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23409step1 raw23409step0; decide +kernel
      have hl : raw23409step1Labels = raw23409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23409step0 raw23409step0Labels permutation80 hz
    mixedMoment B raw23409step1 raw23409step1Labels = mixedMoment B raw23409step2 raw23409step2Labels := by
      have hz : ∀ j, raw23409step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23409step2 = (fun i j => raw23409step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23409step2 raw23409step1; decide +kernel
      have hl : raw23409step2Labels = raw23409step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23409step1 raw23409step1Labels permutation14 hz
    mixedMoment B raw23409step2 raw23409step2Labels = mixedMoment B raw23409step3 raw23409step3Labels := by
      have ha : raw23409step3 = (fun i j => raw23409step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23409step3 raw23409step2; decide +kernel
      have hl : raw23409step3Labels = raw23409step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23409step2 raw23409step2Labels permutation3 permutation7
    mixedMoment B raw23409step3 raw23409step3Labels = mixedMoment B raw23409step4 raw23409step4Labels := by
      have ha : raw23409step4 = -raw23409step3 := by apply Matrix.ext; change ∀ i j, raw23409step4 i j = -(raw23409step3 i j); unfold raw23409step4 raw23409step3; decide +kernel
      have hl : raw23409step4Labels = raw23409step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23409step4 raw23409step4Labels = mixedMoment B raw23409step5 raw23409step5Labels := by
      have ha : raw23409step5 = raw23409step4 := by apply Matrix.ext; unfold raw23409step5 raw23409step4; decide +kernel
      have hl : raw23409step4Labels = labelEmbedding1 ∘ raw23409step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23409step4 raw23409step4Labels raw23409step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1527 node1527Labels := by rfl

def raw23410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23410step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23410step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw23410step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23410step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23410step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23410step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23410step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23410 raw23410Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw23410 raw23410Labels = mixedMoment B raw23410step0 raw23410step0Labels := by
      have hz : ∀ j, raw23410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23410step0 = (fun i j => raw23410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23410step0 raw23410; decide +kernel
      have hl : raw23410step0Labels = raw23410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23410 raw23410Labels permutation434 hz
    mixedMoment B raw23410step0 raw23410step0Labels = mixedMoment B raw23410step1 raw23410step1Labels := by
      have hz : ∀ j, raw23410step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23410step1 = (fun i j => raw23410step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23410step1 raw23410step0; decide +kernel
      have hl : raw23410step1Labels = raw23410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23410step0 raw23410step0Labels permutation80 hz
    mixedMoment B raw23410step1 raw23410step1Labels = mixedMoment B raw23410step2 raw23410step2Labels := by
      have ha : raw23410step2 = (fun i j => raw23410step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23410step2 raw23410step1; decide +kernel
      have hl : raw23410step2Labels = raw23410step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23410step1 raw23410step1Labels permutation9 permutation7
    mixedMoment B raw23410step2 raw23410step2Labels = mixedMoment B raw23410step3 raw23410step3Labels := by
      have ha : raw23410step3 = -raw23410step2 := by apply Matrix.ext; change ∀ i j, raw23410step3 i j = -(raw23410step2 i j); unfold raw23410step3 raw23410step2; decide +kernel
      have hl : raw23410step3Labels = raw23410step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23410step3 raw23410step3Labels = mixedMoment B raw23410step4 raw23410step4Labels := by
      have ha : raw23410step4 = raw23410step3 := by apply Matrix.ext; unfold raw23410step4 raw23410step3; decide +kernel
      have hl : raw23410step3Labels = labelEmbedding1 ∘ raw23410step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23410step3 raw23410step3Labels raw23410step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

def raw23411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23411step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23411step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw23411step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23411step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23411step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23411step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23411step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23411 raw23411Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw23411 raw23411Labels = mixedMoment B raw23411step0 raw23411step0Labels := by
      have hz : ∀ j, raw23411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23411step0 = (fun i j => raw23411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23411step0 raw23411; decide +kernel
      have hl : raw23411step0Labels = raw23411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23411 raw23411Labels permutation434 hz
    mixedMoment B raw23411step0 raw23411step0Labels = mixedMoment B raw23411step1 raw23411step1Labels := by
      have hz : ∀ j, raw23411step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23411step1 = (fun i j => raw23411step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23411step1 raw23411step0; decide +kernel
      have hl : raw23411step1Labels = raw23411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23411step0 raw23411step0Labels permutation56 hz
    mixedMoment B raw23411step1 raw23411step1Labels = mixedMoment B raw23411step2 raw23411step2Labels := by
      have ha : raw23411step2 = (fun i j => raw23411step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23411step2 raw23411step1; decide +kernel
      have hl : raw23411step2Labels = raw23411step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23411step1 raw23411step1Labels permutation9 permutation7
    mixedMoment B raw23411step2 raw23411step2Labels = mixedMoment B raw23411step3 raw23411step3Labels := by
      have ha : raw23411step3 = -raw23411step2 := by apply Matrix.ext; change ∀ i j, raw23411step3 i j = -(raw23411step2 i j); unfold raw23411step3 raw23411step2; decide +kernel
      have hl : raw23411step3Labels = raw23411step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23411step3 raw23411step3Labels = mixedMoment B raw23411step4 raw23411step4Labels := by
      have ha : raw23411step4 = raw23411step3 := by apply Matrix.ext; unfold raw23411step4 raw23411step3; decide +kernel
      have hl : raw23411step3Labels = labelEmbedding1 ∘ raw23411step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23411step3 raw23411step3Labels raw23411step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

def raw23412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23412step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23412step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23412step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw23412step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23412step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23412step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23412step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw23412step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23412 raw23412Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw23412 raw23412Labels = mixedMoment B raw23412step0 raw23412step0Labels := by
      have hz : ∀ j, raw23412 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23412step0 = (fun i j => raw23412 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23412step0 raw23412; decide +kernel
      have hl : raw23412step0Labels = raw23412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23412 raw23412Labels permutation346 hz
    mixedMoment B raw23412step0 raw23412step0Labels = mixedMoment B raw23412step1 raw23412step1Labels := by
      have hz : ∀ j, raw23412step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23412step1 = (fun i j => raw23412step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23412step1 raw23412step0; decide +kernel
      have hl : raw23412step1Labels = raw23412step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23412step0 raw23412step0Labels permutation56 hz
    mixedMoment B raw23412step1 raw23412step1Labels = mixedMoment B raw23412step2 raw23412step2Labels := by
      have ha : raw23412step2 = (fun i j => raw23412step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23412step2 raw23412step1; decide +kernel
      have hl : raw23412step2Labels = raw23412step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23412step1 raw23412step1Labels permutation9 permutation7
    mixedMoment B raw23412step2 raw23412step2Labels = mixedMoment B raw23412step3 raw23412step3Labels := by
      have ha : raw23412step3 = -raw23412step2 := by apply Matrix.ext; change ∀ i j, raw23412step3 i j = -(raw23412step2 i j); unfold raw23412step3 raw23412step2; decide +kernel
      have hl : raw23412step3Labels = raw23412step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23412step3 raw23412step3Labels = mixedMoment B raw23412step4 raw23412step4Labels := by
      have ha : raw23412step4 = raw23412step3 := by apply Matrix.ext; unfold raw23412step4 raw23412step3; decide +kernel
      have hl : raw23412step3Labels = labelEmbedding1 ∘ raw23412step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23412step3 raw23412step3Labels raw23412step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

def raw23413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23413step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw23413step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23413step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![3, 0, -3], ![1, -1, 0]]
def raw23413step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23413step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw23413step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23413step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw23413step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23413step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw23413step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23413 raw23413Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw23413 raw23413Labels = mixedMoment B raw23413step0 raw23413step0Labels := by
      have hz : ∀ j, raw23413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23413step0 = (fun i j => raw23413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23413step0 raw23413; decide +kernel
      have hl : raw23413step0Labels = raw23413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23413 raw23413Labels permutation434 hz
    mixedMoment B raw23413step0 raw23413step0Labels = mixedMoment B raw23413step1 raw23413step1Labels := by
      have hz : ∀ j, raw23413step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23413step1 = (fun i j => raw23413step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23413step1 raw23413step0; decide +kernel
      have hl : raw23413step1Labels = raw23413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23413step0 raw23413step0Labels permutation80 hz
    mixedMoment B raw23413step1 raw23413step1Labels = mixedMoment B raw23413step2 raw23413step2Labels := by
      have hz : ∀ j, raw23413step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23413step2 = (fun i j => raw23413step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23413step2 raw23413step1; decide +kernel
      have hl : raw23413step2Labels = raw23413step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23413step1 raw23413step1Labels permutation14 hz
    mixedMoment B raw23413step2 raw23413step2Labels = mixedMoment B raw23413step3 raw23413step3Labels := by
      have ha : raw23413step3 = (fun i j => raw23413step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23413step3 raw23413step2; decide +kernel
      have hl : raw23413step3Labels = raw23413step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23413step2 raw23413step2Labels permutation3 permutation7
    mixedMoment B raw23413step3 raw23413step3Labels = mixedMoment B raw23413step4 raw23413step4Labels := by
      have ha : raw23413step4 = -raw23413step3 := by apply Matrix.ext; change ∀ i j, raw23413step4 i j = -(raw23413step3 i j); unfold raw23413step4 raw23413step3; decide +kernel
      have hl : raw23413step4Labels = raw23413step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23413step4 raw23413step4Labels = mixedMoment B raw23413step5 raw23413step5Labels := by
      have ha : raw23413step5 = raw23413step4 := by apply Matrix.ext; unfold raw23413step5 raw23413step4; decide +kernel
      have hl : raw23413step4Labels = labelEmbedding1 ∘ raw23413step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23413step4 raw23413step4Labels raw23413step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

def raw23414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23414step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23414step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23414step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw23414step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23414step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-3, 1, 2]]
def raw23414step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23414step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw23414step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23414step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw23414step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23414 raw23414Labels = mixedMoment B node1531 node1531Labels := by
  calc
    mixedMoment B raw23414 raw23414Labels = mixedMoment B raw23414step0 raw23414step0Labels := by
      have hz : ∀ j, raw23414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23414step0 = (fun i j => raw23414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23414step0 raw23414; decide +kernel
      have hl : raw23414step0Labels = raw23414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23414 raw23414Labels permutation434 hz
    mixedMoment B raw23414step0 raw23414step0Labels = mixedMoment B raw23414step1 raw23414step1Labels := by
      have hz : ∀ j, raw23414step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23414step1 = (fun i j => raw23414step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23414step1 raw23414step0; decide +kernel
      have hl : raw23414step1Labels = raw23414step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23414step0 raw23414step0Labels permutation80 hz
    mixedMoment B raw23414step1 raw23414step1Labels = mixedMoment B raw23414step2 raw23414step2Labels := by
      have hz : ∀ j, raw23414step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23414step2 = (fun i j => raw23414step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23414step2 raw23414step1; decide +kernel
      have hl : raw23414step2Labels = raw23414step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23414step1 raw23414step1Labels permutation14 hz
    mixedMoment B raw23414step2 raw23414step2Labels = mixedMoment B raw23414step3 raw23414step3Labels := by
      have ha : raw23414step3 = (fun i j => raw23414step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23414step3 raw23414step2; decide +kernel
      have hl : raw23414step3Labels = raw23414step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23414step2 raw23414step2Labels permutation3 permutation7
    mixedMoment B raw23414step3 raw23414step3Labels = mixedMoment B raw23414step4 raw23414step4Labels := by
      have ha : raw23414step4 = -raw23414step3 := by apply Matrix.ext; change ∀ i j, raw23414step4 i j = -(raw23414step3 i j); unfold raw23414step4 raw23414step3; decide +kernel
      have hl : raw23414step4Labels = raw23414step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23414step4 raw23414step4Labels = mixedMoment B raw23414step5 raw23414step5Labels := by
      have ha : raw23414step5 = raw23414step4 := by apply Matrix.ext; unfold raw23414step5 raw23414step4; decide +kernel
      have hl : raw23414step4Labels = labelEmbedding1 ∘ raw23414step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23414step4 raw23414step4Labels raw23414step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1531 node1531Labels := by rfl

def raw23415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23415step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23415step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw23415step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23415step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23415step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23415step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23415step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23415 raw23415Labels = mixedMoment B node1687 node1687Labels := by
  calc
    mixedMoment B raw23415 raw23415Labels = mixedMoment B raw23415step0 raw23415step0Labels := by
      have hz : ∀ j, raw23415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23415step0 = (fun i j => raw23415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23415step0 raw23415; decide +kernel
      have hl : raw23415step0Labels = raw23415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23415 raw23415Labels permutation434 hz
    mixedMoment B raw23415step0 raw23415step0Labels = mixedMoment B raw23415step1 raw23415step1Labels := by
      have hz : ∀ j, raw23415step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23415step1 = (fun i j => raw23415step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23415step1 raw23415step0; decide +kernel
      have hl : raw23415step1Labels = raw23415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23415step0 raw23415step0Labels permutation80 hz
    mixedMoment B raw23415step1 raw23415step1Labels = mixedMoment B raw23415step2 raw23415step2Labels := by
      have ha : raw23415step2 = (fun i j => raw23415step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23415step2 raw23415step1; decide +kernel
      have hl : raw23415step2Labels = raw23415step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23415step1 raw23415step1Labels permutation9 permutation7
    mixedMoment B raw23415step2 raw23415step2Labels = mixedMoment B raw23415step3 raw23415step3Labels := by
      have ha : raw23415step3 = -raw23415step2 := by apply Matrix.ext; change ∀ i j, raw23415step3 i j = -(raw23415step2 i j); unfold raw23415step3 raw23415step2; decide +kernel
      have hl : raw23415step3Labels = raw23415step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23415step3 raw23415step3Labels = mixedMoment B raw23415step4 raw23415step4Labels := by
      have ha : raw23415step4 = raw23415step3 := by apply Matrix.ext; unfold raw23415step4 raw23415step3; decide +kernel
      have hl : raw23415step3Labels = labelEmbedding1 ∘ raw23415step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23415step3 raw23415step3Labels raw23415step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1687 node1687Labels := by rfl

def raw23416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23416step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23416step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw23416step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23416step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23416step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23416step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23416step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23416 raw23416Labels = mixedMoment B node1687 node1687Labels := by
  calc
    mixedMoment B raw23416 raw23416Labels = mixedMoment B raw23416step0 raw23416step0Labels := by
      have hz : ∀ j, raw23416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23416step0 = (fun i j => raw23416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23416step0 raw23416; decide +kernel
      have hl : raw23416step0Labels = raw23416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23416 raw23416Labels permutation434 hz
    mixedMoment B raw23416step0 raw23416step0Labels = mixedMoment B raw23416step1 raw23416step1Labels := by
      have hz : ∀ j, raw23416step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23416step1 = (fun i j => raw23416step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23416step1 raw23416step0; decide +kernel
      have hl : raw23416step1Labels = raw23416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23416step0 raw23416step0Labels permutation56 hz
    mixedMoment B raw23416step1 raw23416step1Labels = mixedMoment B raw23416step2 raw23416step2Labels := by
      have ha : raw23416step2 = (fun i j => raw23416step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23416step2 raw23416step1; decide +kernel
      have hl : raw23416step2Labels = raw23416step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23416step1 raw23416step1Labels permutation9 permutation7
    mixedMoment B raw23416step2 raw23416step2Labels = mixedMoment B raw23416step3 raw23416step3Labels := by
      have ha : raw23416step3 = -raw23416step2 := by apply Matrix.ext; change ∀ i j, raw23416step3 i j = -(raw23416step2 i j); unfold raw23416step3 raw23416step2; decide +kernel
      have hl : raw23416step3Labels = raw23416step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23416step3 raw23416step3Labels = mixedMoment B raw23416step4 raw23416step4Labels := by
      have ha : raw23416step4 = raw23416step3 := by apply Matrix.ext; unfold raw23416step4 raw23416step3; decide +kernel
      have hl : raw23416step3Labels = labelEmbedding1 ∘ raw23416step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23416step3 raw23416step3Labels raw23416step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1687 node1687Labels := by rfl

def raw23417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23417Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23417step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw23417step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-3, 1, 2]]
def raw23417step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23417step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23417step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw23417step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23417 raw23417Labels = mixedMoment B node1687 node1687Labels := by
  calc
    mixedMoment B raw23417 raw23417Labels = mixedMoment B raw23417step0 raw23417step0Labels := by
      have hz : ∀ j, raw23417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23417step0 = (fun i j => raw23417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23417step0 raw23417; decide +kernel
      have hl : raw23417step0Labels = raw23417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23417 raw23417Labels permutation346 hz
    mixedMoment B raw23417step0 raw23417step0Labels = mixedMoment B raw23417step1 raw23417step1Labels := by
      have hz : ∀ j, raw23417step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23417step1 = (fun i j => raw23417step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23417step1 raw23417step0; decide +kernel
      have hl : raw23417step1Labels = raw23417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23417step0 raw23417step0Labels permutation56 hz
    mixedMoment B raw23417step1 raw23417step1Labels = mixedMoment B raw23417step2 raw23417step2Labels := by
      have ha : raw23417step2 = (fun i j => raw23417step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23417step2 raw23417step1; decide +kernel
      have hl : raw23417step2Labels = raw23417step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23417step1 raw23417step1Labels permutation9 permutation7
    mixedMoment B raw23417step2 raw23417step2Labels = mixedMoment B raw23417step3 raw23417step3Labels := by
      have ha : raw23417step3 = -raw23417step2 := by apply Matrix.ext; change ∀ i j, raw23417step3 i j = -(raw23417step2 i j); unfold raw23417step3 raw23417step2; decide +kernel
      have hl : raw23417step3Labels = raw23417step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23417step3 raw23417step3Labels = mixedMoment B raw23417step4 raw23417step4Labels := by
      have ha : raw23417step4 = raw23417step3 := by apply Matrix.ext; unfold raw23417step4 raw23417step3; decide +kernel
      have hl : raw23417step3Labels = labelEmbedding1 ∘ raw23417step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23417step3 raw23417step3Labels raw23417step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1687 node1687Labels := by rfl

def raw23418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw23418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw23418step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![3, -3, 0]]
def raw23418step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23418step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw23418step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23418step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-3, 2, 1]]
def raw23418step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23418step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw23418step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23418step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw23418step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23418 raw23418Labels = mixedMoment B node1747 node1747Labels := by
  calc
    mixedMoment B raw23418 raw23418Labels = mixedMoment B raw23418step0 raw23418step0Labels := by
      have hz : ∀ j, raw23418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23418step0 = (fun i j => raw23418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23418step0 raw23418; decide +kernel
      have hl : raw23418step0Labels = raw23418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23418 raw23418Labels permutation434 hz
    mixedMoment B raw23418step0 raw23418step0Labels = mixedMoment B raw23418step1 raw23418step1Labels := by
      have hz : ∀ j, raw23418step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23418step1 = (fun i j => raw23418step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23418step1 raw23418step0; decide +kernel
      have hl : raw23418step1Labels = raw23418step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23418step0 raw23418step0Labels permutation80 hz
    mixedMoment B raw23418step1 raw23418step1Labels = mixedMoment B raw23418step2 raw23418step2Labels := by
      have hz : ∀ j, raw23418step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23418step2 = (fun i j => raw23418step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23418step2 raw23418step1; decide +kernel
      have hl : raw23418step2Labels = raw23418step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23418step1 raw23418step1Labels permutation14 hz
    mixedMoment B raw23418step2 raw23418step2Labels = mixedMoment B raw23418step3 raw23418step3Labels := by
      have ha : raw23418step3 = (fun i j => raw23418step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23418step3 raw23418step2; decide +kernel
      have hl : raw23418step3Labels = raw23418step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23418step2 raw23418step2Labels permutation3 permutation7
    mixedMoment B raw23418step3 raw23418step3Labels = mixedMoment B raw23418step4 raw23418step4Labels := by
      have ha : raw23418step4 = -raw23418step3 := by apply Matrix.ext; change ∀ i j, raw23418step4 i j = -(raw23418step3 i j); unfold raw23418step4 raw23418step3; decide +kernel
      have hl : raw23418step4Labels = raw23418step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23418step4 raw23418step4Labels = mixedMoment B raw23418step5 raw23418step5Labels := by
      have ha : raw23418step5 = raw23418step4 := by apply Matrix.ext; unfold raw23418step5 raw23418step4; decide +kernel
      have hl : raw23418step4Labels = labelEmbedding1 ∘ raw23418step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23418step4 raw23418step4Labels raw23418step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1747 node1747Labels := by rfl

def raw23419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23419 raw23419Labels = mixedMoment B node607 node607Labels := by
  calc
    mixedMoment B raw23419 raw23419Labels = mixedMoment B raw23419step0 raw23419step0Labels := by
      have hz : ∀ j, raw23419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23419step0 = (fun i j => raw23419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23419step0 raw23419; decide +kernel
      have hl : raw23419step0Labels = raw23419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23419 raw23419Labels permutation434 hz
    mixedMoment B raw23419step0 raw23419step0Labels = mixedMoment B raw23419step1 raw23419step1Labels := by
      have hz : ∀ j, raw23419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23419step1 = (fun i j => raw23419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23419step1 raw23419step0; decide +kernel
      have hl : raw23419step1Labels = raw23419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23419step0 raw23419step0Labels permutation80 hz
    mixedMoment B raw23419step1 raw23419step1Labels = mixedMoment B raw23419step2 raw23419step2Labels := by
      have ha : raw23419step2 = (fun i j => raw23419step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23419step2 raw23419step1; decide +kernel
      have hl : raw23419step2Labels = raw23419step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23419step1 raw23419step1Labels permutation9 permutation2
    _ = mixedMoment B node607 node607Labels := by rfl

def raw23420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23420 raw23420Labels = mixedMoment B node607 node607Labels := by
  calc
    mixedMoment B raw23420 raw23420Labels = mixedMoment B raw23420step0 raw23420step0Labels := by
      have hz : ∀ j, raw23420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23420step0 = (fun i j => raw23420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23420step0 raw23420; decide +kernel
      have hl : raw23420step0Labels = raw23420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23420 raw23420Labels permutation434 hz
    mixedMoment B raw23420step0 raw23420step0Labels = mixedMoment B raw23420step1 raw23420step1Labels := by
      have hz : ∀ j, raw23420step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23420step1 = (fun i j => raw23420step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23420step1 raw23420step0; decide +kernel
      have hl : raw23420step1Labels = raw23420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23420step0 raw23420step0Labels permutation56 hz
    mixedMoment B raw23420step1 raw23420step1Labels = mixedMoment B raw23420step2 raw23420step2Labels := by
      have ha : raw23420step2 = (fun i j => raw23420step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23420step2 raw23420step1; decide +kernel
      have hl : raw23420step2Labels = raw23420step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23420step1 raw23420step1Labels permutation9 permutation2
    _ = mixedMoment B node607 node607Labels := by rfl

def raw23421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23421 raw23421Labels = mixedMoment B node607 node607Labels := by
  calc
    mixedMoment B raw23421 raw23421Labels = mixedMoment B raw23421step0 raw23421step0Labels := by
      have hz : ∀ j, raw23421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23421step0 = (fun i j => raw23421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23421step0 raw23421; decide +kernel
      have hl : raw23421step0Labels = raw23421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23421 raw23421Labels permutation346 hz
    mixedMoment B raw23421step0 raw23421step0Labels = mixedMoment B raw23421step1 raw23421step1Labels := by
      have hz : ∀ j, raw23421step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23421step1 = (fun i j => raw23421step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23421step1 raw23421step0; decide +kernel
      have hl : raw23421step1Labels = raw23421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23421step0 raw23421step0Labels permutation56 hz
    mixedMoment B raw23421step1 raw23421step1Labels = mixedMoment B raw23421step2 raw23421step2Labels := by
      have ha : raw23421step2 = (fun i j => raw23421step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23421step2 raw23421step1; decide +kernel
      have hl : raw23421step2Labels = raw23421step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23421step1 raw23421step1Labels permutation9 permutation2
    _ = mixedMoment B node607 node607Labels := by rfl

def raw23422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw23422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![3, 0, -3], ![2, -2, 0]]
def raw23422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23422step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw23422step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23422 raw23422Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw23422 raw23422Labels = mixedMoment B raw23422step0 raw23422step0Labels := by
      have hz : ∀ j, raw23422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23422step0 = (fun i j => raw23422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23422step0 raw23422; decide +kernel
      have hl : raw23422step0Labels = raw23422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23422 raw23422Labels permutation434 hz
    mixedMoment B raw23422step0 raw23422step0Labels = mixedMoment B raw23422step1 raw23422step1Labels := by
      have hz : ∀ j, raw23422step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23422step1 = (fun i j => raw23422step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23422step1 raw23422step0; decide +kernel
      have hl : raw23422step1Labels = raw23422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23422step0 raw23422step0Labels permutation80 hz
    mixedMoment B raw23422step1 raw23422step1Labels = mixedMoment B raw23422step2 raw23422step2Labels := by
      have hz : ∀ j, raw23422step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23422step2 = (fun i j => raw23422step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23422step2 raw23422step1; decide +kernel
      have hl : raw23422step2Labels = raw23422step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23422step1 raw23422step1Labels permutation14 hz
    mixedMoment B raw23422step2 raw23422step2Labels = mixedMoment B raw23422step3 raw23422step3Labels := by
      have ha : raw23422step3 = (fun i j => raw23422step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23422step3 raw23422step2; decide +kernel
      have hl : raw23422step3Labels = raw23422step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23422step2 raw23422step2Labels permutation3 permutation2
    _ = mixedMoment B node618 node618Labels := by rfl

def raw23423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw23423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23423 raw23423Labels = mixedMoment B node926 node926Labels := by
  calc
    mixedMoment B raw23423 raw23423Labels = mixedMoment B raw23423step0 raw23423step0Labels := by
      have hz : ∀ j, raw23423 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23423step0 = (fun i j => raw23423 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23423step0 raw23423; decide +kernel
      have hl : raw23423step0Labels = raw23423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23423 raw23423Labels permutation434 hz
    mixedMoment B raw23423step0 raw23423step0Labels = mixedMoment B raw23423step1 raw23423step1Labels := by
      have ha : raw23423step1 = (fun i j => raw23423step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23423step1 raw23423step0; decide +kernel
      have hl : raw23423step1Labels = raw23423step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23423step0 raw23423step0Labels permutation39 permutation2
    _ = mixedMoment B node926 node926Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
