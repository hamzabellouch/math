import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29568 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29568step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29568 raw29568Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw29568 raw29568Labels = mixedMoment B raw29568step0 raw29568step0Labels := by
      have hz : ∀ j, raw29568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29568step0 = (fun i j => raw29568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29568step0 raw29568; decide +kernel
      have hl : raw29568step0Labels = raw29568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29568 raw29568Labels permutation434 hz
    mixedMoment B raw29568step0 raw29568step0Labels = mixedMoment B raw29568step1 raw29568step1Labels := by
      have ha : raw29568step1 = (fun i j => raw29568step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29568step1 raw29568step0; decide +kernel
      have hl : raw29568step1Labels = raw29568step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29568step0 raw29568step0Labels permutation32 permutation6
    mixedMoment B raw29568step1 raw29568step1Labels = mixedMoment B raw29568step2 raw29568step2Labels := by
      have ha : raw29568step2 = raw29568step1 := by apply Matrix.ext; unfold raw29568step2 raw29568step1; decide +kernel
      have hl : raw29568step1Labels = labelEmbedding9 ∘ raw29568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29568step1 raw29568step1Labels raw29568step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw29569 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29569step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29569 raw29569Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw29569 raw29569Labels = mixedMoment B raw29569step0 raw29569step0Labels := by
      have hz : ∀ j, raw29569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29569step0 = (fun i j => raw29569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29569step0 raw29569; decide +kernel
      have hl : raw29569step0Labels = raw29569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29569 raw29569Labels permutation346 hz
    mixedMoment B raw29569step0 raw29569step0Labels = mixedMoment B raw29569step1 raw29569step1Labels := by
      have ha : raw29569step1 = (fun i j => raw29569step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29569step1 raw29569step0; decide +kernel
      have hl : raw29569step1Labels = raw29569step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29569step0 raw29569step0Labels permutation32 permutation6
    mixedMoment B raw29569step1 raw29569step1Labels = mixedMoment B raw29569step2 raw29569step2Labels := by
      have ha : raw29569step2 = raw29569step1 := by apply Matrix.ext; unfold raw29569step2 raw29569step1; decide +kernel
      have hl : raw29569step1Labels = labelEmbedding9 ∘ raw29569step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29569step1 raw29569step1Labels raw29569step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw29570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-3, 1, 2], ![0, -2, 2]]
def raw29570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29570step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29570step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29570step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29570step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29570 raw29570Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw29570 raw29570Labels = mixedMoment B raw29570step0 raw29570step0Labels := by
      have hz : ∀ j, raw29570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29570step0 = (fun i j => raw29570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29570step0 raw29570; decide +kernel
      have hl : raw29570step0Labels = raw29570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29570 raw29570Labels permutation434 hz
    mixedMoment B raw29570step0 raw29570step0Labels = mixedMoment B raw29570step1 raw29570step1Labels := by
      have hz : ∀ j, raw29570step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29570step1 = (fun i j => raw29570step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29570step1 raw29570step0; decide +kernel
      have hl : raw29570step1Labels = raw29570step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29570step0 raw29570step0Labels permutation80 hz
    mixedMoment B raw29570step1 raw29570step1Labels = mixedMoment B raw29570step2 raw29570step2Labels := by
      have ha : raw29570step2 = (fun i j => raw29570step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29570step2 raw29570step1; decide +kernel
      have hl : raw29570step2Labels = raw29570step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29570step1 raw29570step1Labels permutation8 permutation6
    mixedMoment B raw29570step2 raw29570step2Labels = mixedMoment B raw29570step3 raw29570step3Labels := by
      have ha : raw29570step3 = raw29570step2 := by apply Matrix.ext; unfold raw29570step3 raw29570step2; decide +kernel
      have hl : raw29570step2Labels = labelEmbedding9 ∘ raw29570step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29570step2 raw29570step2Labels raw29570step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw29571 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29571step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29571step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29571step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29571 raw29571Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw29571 raw29571Labels = mixedMoment B raw29571step0 raw29571step0Labels := by
      have hz : ∀ j, raw29571 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29571step0 = (fun i j => raw29571 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29571step0 raw29571; decide +kernel
      have hl : raw29571step0Labels = raw29571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29571 raw29571Labels permutation434 hz
    mixedMoment B raw29571step0 raw29571step0Labels = mixedMoment B raw29571step1 raw29571step1Labels := by
      have hz : ∀ j, raw29571step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29571step1 = (fun i j => raw29571step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29571step1 raw29571step0; decide +kernel
      have hl : raw29571step1Labels = raw29571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29571step0 raw29571step0Labels permutation80 hz
    mixedMoment B raw29571step1 raw29571step1Labels = mixedMoment B raw29571step2 raw29571step2Labels := by
      have ha : raw29571step2 = (fun i j => raw29571step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29571step2 raw29571step1; decide +kernel
      have hl : raw29571step2Labels = raw29571step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29571step1 raw29571step1Labels permutation8 permutation6
    mixedMoment B raw29571step2 raw29571step2Labels = mixedMoment B raw29571step3 raw29571step3Labels := by
      have ha : raw29571step3 = raw29571step2 := by apply Matrix.ext; unfold raw29571step3 raw29571step2; decide +kernel
      have hl : raw29571step2Labels = labelEmbedding9 ∘ raw29571step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29571step2 raw29571step2Labels raw29571step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw29572 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29572step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29572 raw29572Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw29572 raw29572Labels = mixedMoment B raw29572step0 raw29572step0Labels := by
      have hz : ∀ j, raw29572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29572step0 = (fun i j => raw29572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29572step0 raw29572; decide +kernel
      have hl : raw29572step0Labels = raw29572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29572 raw29572Labels permutation434 hz
    mixedMoment B raw29572step0 raw29572step0Labels = mixedMoment B raw29572step1 raw29572step1Labels := by
      have ha : raw29572step1 = (fun i j => raw29572step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29572step1 raw29572step0; decide +kernel
      have hl : raw29572step1Labels = raw29572step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29572step0 raw29572step0Labels permutation32 permutation6
    mixedMoment B raw29572step1 raw29572step1Labels = mixedMoment B raw29572step2 raw29572step2Labels := by
      have ha : raw29572step2 = raw29572step1 := by apply Matrix.ext; unfold raw29572step2 raw29572step1; decide +kernel
      have hl : raw29572step1Labels = labelEmbedding9 ∘ raw29572step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29572step1 raw29572step1Labels raw29572step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw29573 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29573step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29573step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29573 raw29573Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw29573 raw29573Labels = mixedMoment B raw29573step0 raw29573step0Labels := by
      have hz : ∀ j, raw29573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29573step0 = (fun i j => raw29573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29573step0 raw29573; decide +kernel
      have hl : raw29573step0Labels = raw29573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29573 raw29573Labels permutation434 hz
    mixedMoment B raw29573step0 raw29573step0Labels = mixedMoment B raw29573step1 raw29573step1Labels := by
      have ha : raw29573step1 = (fun i j => raw29573step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29573step1 raw29573step0; decide +kernel
      have hl : raw29573step1Labels = raw29573step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29573step0 raw29573step0Labels permutation32 permutation6
    mixedMoment B raw29573step1 raw29573step1Labels = mixedMoment B raw29573step2 raw29573step2Labels := by
      have ha : raw29573step2 = raw29573step1 := by apply Matrix.ext; unfold raw29573step2 raw29573step1; decide +kernel
      have hl : raw29573step1Labels = labelEmbedding9 ∘ raw29573step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29573step1 raw29573step1Labels raw29573step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw29574 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29574step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29574 raw29574Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw29574 raw29574Labels = mixedMoment B raw29574step0 raw29574step0Labels := by
      have ha : raw29574step0 = (fun i j => raw29574 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29574step0 raw29574; decide +kernel
      have hl : raw29574step0Labels = raw29574Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29574 raw29574Labels permutation158 permutation6
    mixedMoment B raw29574step0 raw29574step0Labels = mixedMoment B raw29574step1 raw29574step1Labels := by
      have ha : raw29574step1 = raw29574step0 := by apply Matrix.ext; unfold raw29574step1 raw29574step0; decide +kernel
      have hl : raw29574step0Labels = labelEmbedding9 ∘ raw29574step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29574step0 raw29574step0Labels raw29574step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw29575 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29575step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29575 raw29575Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw29575 raw29575Labels = mixedMoment B raw29575step0 raw29575step0Labels := by
      have hz : ∀ j, raw29575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29575step0 = (fun i j => raw29575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29575step0 raw29575; decide +kernel
      have hl : raw29575step0Labels = raw29575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29575 raw29575Labels permutation434 hz
    mixedMoment B raw29575step0 raw29575step0Labels = mixedMoment B raw29575step1 raw29575step1Labels := by
      have ha : raw29575step1 = (fun i j => raw29575step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29575step1 raw29575step0; decide +kernel
      have hl : raw29575step1Labels = raw29575step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29575step0 raw29575step0Labels permutation32 permutation6
    mixedMoment B raw29575step1 raw29575step1Labels = mixedMoment B raw29575step2 raw29575step2Labels := by
      have ha : raw29575step2 = raw29575step1 := by apply Matrix.ext; unfold raw29575step2 raw29575step1; decide +kernel
      have hl : raw29575step1Labels = labelEmbedding9 ∘ raw29575step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29575step1 raw29575step1Labels raw29575step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw29576 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29576step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29576 raw29576Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw29576 raw29576Labels = mixedMoment B raw29576step0 raw29576step0Labels := by
      have hz : ∀ j, raw29576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29576step0 = (fun i j => raw29576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29576step0 raw29576; decide +kernel
      have hl : raw29576step0Labels = raw29576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29576 raw29576Labels permutation434 hz
    mixedMoment B raw29576step0 raw29576step0Labels = mixedMoment B raw29576step1 raw29576step1Labels := by
      have ha : raw29576step1 = (fun i j => raw29576step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29576step1 raw29576step0; decide +kernel
      have hl : raw29576step1Labels = raw29576step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29576step0 raw29576step0Labels permutation32 permutation6
    mixedMoment B raw29576step1 raw29576step1Labels = mixedMoment B raw29576step2 raw29576step2Labels := by
      have ha : raw29576step2 = raw29576step1 := by apply Matrix.ext; unfold raw29576step2 raw29576step1; decide +kernel
      have hl : raw29576step1Labels = labelEmbedding9 ∘ raw29576step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29576step1 raw29576step1Labels raw29576step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw29577 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29577step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29577step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29577 raw29577Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw29577 raw29577Labels = mixedMoment B raw29577step0 raw29577step0Labels := by
      have hz : ∀ j, raw29577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29577step0 = (fun i j => raw29577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29577step0 raw29577; decide +kernel
      have hl : raw29577step0Labels = raw29577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29577 raw29577Labels permutation346 hz
    mixedMoment B raw29577step0 raw29577step0Labels = mixedMoment B raw29577step1 raw29577step1Labels := by
      have ha : raw29577step1 = (fun i j => raw29577step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29577step1 raw29577step0; decide +kernel
      have hl : raw29577step1Labels = raw29577step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29577step0 raw29577step0Labels permutation32 permutation6
    mixedMoment B raw29577step1 raw29577step1Labels = mixedMoment B raw29577step2 raw29577step2Labels := by
      have ha : raw29577step2 = raw29577step1 := by apply Matrix.ext; unfold raw29577step2 raw29577step1; decide +kernel
      have hl : raw29577step1Labels = labelEmbedding9 ∘ raw29577step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29577step1 raw29577step1Labels raw29577step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw29578 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29578step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29578step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29578 raw29578Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw29578 raw29578Labels = mixedMoment B raw29578step0 raw29578step0Labels := by
      have hz : ∀ j, raw29578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29578step0 = (fun i j => raw29578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29578step0 raw29578; decide +kernel
      have hl : raw29578step0Labels = raw29578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29578 raw29578Labels permutation346 hz
    mixedMoment B raw29578step0 raw29578step0Labels = mixedMoment B raw29578step1 raw29578step1Labels := by
      have ha : raw29578step1 = (fun i j => raw29578step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29578step1 raw29578step0; decide +kernel
      have hl : raw29578step1Labels = raw29578step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29578step0 raw29578step0Labels permutation32 permutation6
    mixedMoment B raw29578step1 raw29578step1Labels = mixedMoment B raw29578step2 raw29578step2Labels := by
      have ha : raw29578step2 = raw29578step1 := by apply Matrix.ext; unfold raw29578step2 raw29578step1; decide +kernel
      have hl : raw29578step1Labels = labelEmbedding9 ∘ raw29578step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29578step1 raw29578step1Labels raw29578step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw29579 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29579step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29579 raw29579Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw29579 raw29579Labels = mixedMoment B raw29579step0 raw29579step0Labels := by
      have ha : raw29579step0 = (fun i j => raw29579 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29579step0 raw29579; decide +kernel
      have hl : raw29579step0Labels = raw29579Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29579 raw29579Labels permutation152 permutation6
    mixedMoment B raw29579step0 raw29579step0Labels = mixedMoment B raw29579step1 raw29579step1Labels := by
      have ha : raw29579step1 = raw29579step0 := by apply Matrix.ext; unfold raw29579step1 raw29579step0; decide +kernel
      have hl : raw29579step0Labels = labelEmbedding9 ∘ raw29579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29579step0 raw29579step0Labels raw29579step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw29580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29580step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29580 raw29580Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw29580 raw29580Labels = mixedMoment B raw29580step0 raw29580step0Labels := by
      have hz : ∀ j, raw29580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29580step0 = (fun i j => raw29580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29580step0 raw29580; decide +kernel
      have hl : raw29580step0Labels = raw29580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29580 raw29580Labels permutation346 hz
    mixedMoment B raw29580step0 raw29580step0Labels = mixedMoment B raw29580step1 raw29580step1Labels := by
      have ha : raw29580step1 = (fun i j => raw29580step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29580step1 raw29580step0; decide +kernel
      have hl : raw29580step1Labels = raw29580step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29580step0 raw29580step0Labels permutation32 permutation6
    mixedMoment B raw29580step1 raw29580step1Labels = mixedMoment B raw29580step2 raw29580step2Labels := by
      have ha : raw29580step2 = raw29580step1 := by apply Matrix.ext; unfold raw29580step2 raw29580step1; decide +kernel
      have hl : raw29580step1Labels = labelEmbedding9 ∘ raw29580step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29580step1 raw29580step1Labels raw29580step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw29581 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29581step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29581step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29581 raw29581Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw29581 raw29581Labels = mixedMoment B raw29581step0 raw29581step0Labels := by
      have hz : ∀ j, raw29581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29581step0 = (fun i j => raw29581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29581step0 raw29581; decide +kernel
      have hl : raw29581step0Labels = raw29581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29581 raw29581Labels permutation346 hz
    mixedMoment B raw29581step0 raw29581step0Labels = mixedMoment B raw29581step1 raw29581step1Labels := by
      have ha : raw29581step1 = (fun i j => raw29581step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29581step1 raw29581step0; decide +kernel
      have hl : raw29581step1Labels = raw29581step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29581step0 raw29581step0Labels permutation32 permutation6
    mixedMoment B raw29581step1 raw29581step1Labels = mixedMoment B raw29581step2 raw29581step2Labels := by
      have ha : raw29581step2 = raw29581step1 := by apply Matrix.ext; unfold raw29581step2 raw29581step1; decide +kernel
      have hl : raw29581step1Labels = labelEmbedding9 ∘ raw29581step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29581step1 raw29581step1Labels raw29581step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw29582 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw29582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29582step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29582step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29582step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29582 raw29582Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw29582 raw29582Labels = mixedMoment B raw29582step0 raw29582step0Labels := by
      have hz : ∀ j, raw29582 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29582step0 = (fun i j => raw29582 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29582step0 raw29582; decide +kernel
      have hl : raw29582step0Labels = raw29582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29582 raw29582Labels permutation434 hz
    mixedMoment B raw29582step0 raw29582step0Labels = mixedMoment B raw29582step1 raw29582step1Labels := by
      have hz : ∀ j, raw29582step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29582step1 = (fun i j => raw29582step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29582step1 raw29582step0; decide +kernel
      have hl : raw29582step1Labels = raw29582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29582step0 raw29582step0Labels permutation80 hz
    mixedMoment B raw29582step1 raw29582step1Labels = mixedMoment B raw29582step2 raw29582step2Labels := by
      have ha : raw29582step2 = (fun i j => raw29582step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29582step2 raw29582step1; decide +kernel
      have hl : raw29582step2Labels = raw29582step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29582step1 raw29582step1Labels permutation8 permutation6
    mixedMoment B raw29582step2 raw29582step2Labels = mixedMoment B raw29582step3 raw29582step3Labels := by
      have ha : raw29582step3 = raw29582step2 := by apply Matrix.ext; unfold raw29582step3 raw29582step2; decide +kernel
      have hl : raw29582step2Labels = labelEmbedding9 ∘ raw29582step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29582step2 raw29582step2Labels raw29582step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw29583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw29583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29583step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29583step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29583 raw29583Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw29583 raw29583Labels = mixedMoment B raw29583step0 raw29583step0Labels := by
      have hz : ∀ j, raw29583 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29583step0 = (fun i j => raw29583 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29583step0 raw29583; decide +kernel
      have hl : raw29583step0Labels = raw29583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29583 raw29583Labels permutation434 hz
    mixedMoment B raw29583step0 raw29583step0Labels = mixedMoment B raw29583step1 raw29583step1Labels := by
      have hz : ∀ j, raw29583step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29583step1 = (fun i j => raw29583step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29583step1 raw29583step0; decide +kernel
      have hl : raw29583step1Labels = raw29583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29583step0 raw29583step0Labels permutation80 hz
    mixedMoment B raw29583step1 raw29583step1Labels = mixedMoment B raw29583step2 raw29583step2Labels := by
      have ha : raw29583step2 = (fun i j => raw29583step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29583step2 raw29583step1; decide +kernel
      have hl : raw29583step2Labels = raw29583step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29583step1 raw29583step1Labels permutation8 permutation6
    mixedMoment B raw29583step2 raw29583step2Labels = mixedMoment B raw29583step3 raw29583step3Labels := by
      have ha : raw29583step3 = raw29583step2 := by apply Matrix.ext; unfold raw29583step3 raw29583step2; decide +kernel
      have hl : raw29583step2Labels = labelEmbedding9 ∘ raw29583step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29583step2 raw29583step2Labels raw29583step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5111 node5111Labels := by rfl

def raw29584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29584step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29584step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29584step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29584 raw29584Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw29584 raw29584Labels = mixedMoment B raw29584step0 raw29584step0Labels := by
      have hz : ∀ j, raw29584 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29584step0 = (fun i j => raw29584 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29584step0 raw29584; decide +kernel
      have hl : raw29584step0Labels = raw29584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29584 raw29584Labels permutation434 hz
    mixedMoment B raw29584step0 raw29584step0Labels = mixedMoment B raw29584step1 raw29584step1Labels := by
      have ha : raw29584step1 = (fun i j => raw29584step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29584step1 raw29584step0; decide +kernel
      have hl : raw29584step1Labels = raw29584step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29584step0 raw29584step0Labels permutation32 permutation6
    mixedMoment B raw29584step1 raw29584step1Labels = mixedMoment B raw29584step2 raw29584step2Labels := by
      have ha : raw29584step2 = raw29584step1 := by apply Matrix.ext; unfold raw29584step2 raw29584step1; decide +kernel
      have hl : raw29584step1Labels = labelEmbedding9 ∘ raw29584step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29584step1 raw29584step1Labels raw29584step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw29585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29585step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29585step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29585 raw29585Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw29585 raw29585Labels = mixedMoment B raw29585step0 raw29585step0Labels := by
      have hz : ∀ j, raw29585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29585step0 = (fun i j => raw29585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29585step0 raw29585; decide +kernel
      have hl : raw29585step0Labels = raw29585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29585 raw29585Labels permutation346 hz
    mixedMoment B raw29585step0 raw29585step0Labels = mixedMoment B raw29585step1 raw29585step1Labels := by
      have ha : raw29585step1 = (fun i j => raw29585step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29585step1 raw29585step0; decide +kernel
      have hl : raw29585step1Labels = raw29585step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29585step0 raw29585step0Labels permutation32 permutation6
    mixedMoment B raw29585step1 raw29585step1Labels = mixedMoment B raw29585step2 raw29585step2Labels := by
      have ha : raw29585step2 = raw29585step1 := by apply Matrix.ext; unfold raw29585step2 raw29585step1; decide +kernel
      have hl : raw29585step1Labels = labelEmbedding9 ∘ raw29585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29585step1 raw29585step1Labels raw29585step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw29586 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29586step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29586step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29586 raw29586Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw29586 raw29586Labels = mixedMoment B raw29586step0 raw29586step0Labels := by
      have hz : ∀ j, raw29586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29586step0 = (fun i j => raw29586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29586step0 raw29586; decide +kernel
      have hl : raw29586step0Labels = raw29586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29586 raw29586Labels permutation434 hz
    mixedMoment B raw29586step0 raw29586step0Labels = mixedMoment B raw29586step1 raw29586step1Labels := by
      have hz : ∀ j, raw29586step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29586step1 = (fun i j => raw29586step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29586step1 raw29586step0; decide +kernel
      have hl : raw29586step1Labels = raw29586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29586step0 raw29586step0Labels permutation80 hz
    mixedMoment B raw29586step1 raw29586step1Labels = mixedMoment B raw29586step2 raw29586step2Labels := by
      have ha : raw29586step2 = (fun i j => raw29586step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29586step2 raw29586step1; decide +kernel
      have hl : raw29586step2Labels = raw29586step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29586step1 raw29586step1Labels permutation8 permutation6
    mixedMoment B raw29586step2 raw29586step2Labels = mixedMoment B raw29586step3 raw29586step3Labels := by
      have ha : raw29586step3 = raw29586step2 := by apply Matrix.ext; unfold raw29586step3 raw29586step2; decide +kernel
      have hl : raw29586step2Labels = labelEmbedding9 ∘ raw29586step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29586step2 raw29586step2Labels raw29586step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw29587 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 0, 2], ![1, -3, 2]]
def raw29587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29587step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29587step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29587step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29587 raw29587Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw29587 raw29587Labels = mixedMoment B raw29587step0 raw29587step0Labels := by
      have hz : ∀ j, raw29587 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29587step0 = (fun i j => raw29587 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29587step0 raw29587; decide +kernel
      have hl : raw29587step0Labels = raw29587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29587 raw29587Labels permutation434 hz
    mixedMoment B raw29587step0 raw29587step0Labels = mixedMoment B raw29587step1 raw29587step1Labels := by
      have hz : ∀ j, raw29587step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29587step1 = (fun i j => raw29587step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29587step1 raw29587step0; decide +kernel
      have hl : raw29587step1Labels = raw29587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29587step0 raw29587step0Labels permutation80 hz
    mixedMoment B raw29587step1 raw29587step1Labels = mixedMoment B raw29587step2 raw29587step2Labels := by
      have ha : raw29587step2 = (fun i j => raw29587step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29587step2 raw29587step1; decide +kernel
      have hl : raw29587step2Labels = raw29587step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29587step1 raw29587step1Labels permutation8 permutation6
    mixedMoment B raw29587step2 raw29587step2Labels = mixedMoment B raw29587step3 raw29587step3Labels := by
      have ha : raw29587step3 = raw29587step2 := by apply Matrix.ext; unfold raw29587step3 raw29587step2; decide +kernel
      have hl : raw29587step2Labels = labelEmbedding9 ∘ raw29587step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29587step2 raw29587step2Labels raw29587step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw29588 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 0, 2], ![1, -3, 2]]
def raw29588step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29588step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29588step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29588step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29588 raw29588Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw29588 raw29588Labels = mixedMoment B raw29588step0 raw29588step0Labels := by
      have hz : ∀ j, raw29588 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29588step0 = (fun i j => raw29588 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29588step0 raw29588; decide +kernel
      have hl : raw29588step0Labels = raw29588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29588 raw29588Labels permutation434 hz
    mixedMoment B raw29588step0 raw29588step0Labels = mixedMoment B raw29588step1 raw29588step1Labels := by
      have hz : ∀ j, raw29588step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29588step1 = (fun i j => raw29588step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29588step1 raw29588step0; decide +kernel
      have hl : raw29588step1Labels = raw29588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29588step0 raw29588step0Labels permutation80 hz
    mixedMoment B raw29588step1 raw29588step1Labels = mixedMoment B raw29588step2 raw29588step2Labels := by
      have ha : raw29588step2 = (fun i j => raw29588step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29588step2 raw29588step1; decide +kernel
      have hl : raw29588step2Labels = raw29588step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29588step1 raw29588step1Labels permutation8 permutation6
    mixedMoment B raw29588step2 raw29588step2Labels = mixedMoment B raw29588step3 raw29588step3Labels := by
      have ha : raw29588step3 = raw29588step2 := by apply Matrix.ext; unfold raw29588step3 raw29588step2; decide +kernel
      have hl : raw29588step2Labels = labelEmbedding9 ∘ raw29588step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29588step2 raw29588step2Labels raw29588step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw29589 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29589step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29589step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29589step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29589 raw29589Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw29589 raw29589Labels = mixedMoment B raw29589step0 raw29589step0Labels := by
      have hz : ∀ j, raw29589 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29589step0 = (fun i j => raw29589 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29589step0 raw29589; decide +kernel
      have hl : raw29589step0Labels = raw29589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29589 raw29589Labels permutation434 hz
    mixedMoment B raw29589step0 raw29589step0Labels = mixedMoment B raw29589step1 raw29589step1Labels := by
      have ha : raw29589step1 = (fun i j => raw29589step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29589step1 raw29589step0; decide +kernel
      have hl : raw29589step1Labels = raw29589step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29589step0 raw29589step0Labels permutation32 permutation6
    mixedMoment B raw29589step1 raw29589step1Labels = mixedMoment B raw29589step2 raw29589step2Labels := by
      have ha : raw29589step2 = raw29589step1 := by apply Matrix.ext; unfold raw29589step2 raw29589step1; decide +kernel
      have hl : raw29589step1Labels = labelEmbedding9 ∘ raw29589step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29589step1 raw29589step1Labels raw29589step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw29590 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29590step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29590step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29590 raw29590Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw29590 raw29590Labels = mixedMoment B raw29590step0 raw29590step0Labels := by
      have hz : ∀ j, raw29590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29590step0 = (fun i j => raw29590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29590step0 raw29590; decide +kernel
      have hl : raw29590step0Labels = raw29590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29590 raw29590Labels permutation346 hz
    mixedMoment B raw29590step0 raw29590step0Labels = mixedMoment B raw29590step1 raw29590step1Labels := by
      have ha : raw29590step1 = (fun i j => raw29590step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29590step1 raw29590step0; decide +kernel
      have hl : raw29590step1Labels = raw29590step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29590step0 raw29590step0Labels permutation32 permutation6
    mixedMoment B raw29590step1 raw29590step1Labels = mixedMoment B raw29590step2 raw29590step2Labels := by
      have ha : raw29590step2 = raw29590step1 := by apply Matrix.ext; unfold raw29590step2 raw29590step1; decide +kernel
      have hl : raw29590step1Labels = labelEmbedding9 ∘ raw29590step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29590step1 raw29590step1Labels raw29590step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw29591 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-3, 1, 2], ![1, -3, 2]]
def raw29591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw29591step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29591step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw29591step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29591 raw29591Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw29591 raw29591Labels = mixedMoment B raw29591step0 raw29591step0Labels := by
      have hz : ∀ j, raw29591 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29591step0 = (fun i j => raw29591 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29591step0 raw29591; decide +kernel
      have hl : raw29591step0Labels = raw29591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29591 raw29591Labels permutation434 hz
    mixedMoment B raw29591step0 raw29591step0Labels = mixedMoment B raw29591step1 raw29591step1Labels := by
      have hz : ∀ j, raw29591step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29591step1 = (fun i j => raw29591step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29591step1 raw29591step0; decide +kernel
      have hl : raw29591step1Labels = raw29591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29591step0 raw29591step0Labels permutation80 hz
    mixedMoment B raw29591step1 raw29591step1Labels = mixedMoment B raw29591step2 raw29591step2Labels := by
      have ha : raw29591step2 = (fun i j => raw29591step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29591step2 raw29591step1; decide +kernel
      have hl : raw29591step2Labels = raw29591step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29591step1 raw29591step1Labels permutation8 permutation6
    mixedMoment B raw29591step2 raw29591step2Labels = mixedMoment B raw29591step3 raw29591step3Labels := by
      have ha : raw29591step3 = raw29591step2 := by apply Matrix.ext; unfold raw29591step3 raw29591step2; decide +kernel
      have hl : raw29591step2Labels = labelEmbedding9 ∘ raw29591step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29591step2 raw29591step2Labels raw29591step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw29592 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29592step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29592step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29592step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29592step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29592step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29592 raw29592Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw29592 raw29592Labels = mixedMoment B raw29592step0 raw29592step0Labels := by
      have hz : ∀ j, raw29592 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29592step0 = (fun i j => raw29592 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29592step0 raw29592; decide +kernel
      have hl : raw29592step0Labels = raw29592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29592 raw29592Labels permutation434 hz
    mixedMoment B raw29592step0 raw29592step0Labels = mixedMoment B raw29592step1 raw29592step1Labels := by
      have hz : ∀ j, raw29592step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29592step1 = (fun i j => raw29592step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29592step1 raw29592step0; decide +kernel
      have hl : raw29592step1Labels = raw29592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29592step0 raw29592step0Labels permutation80 hz
    mixedMoment B raw29592step1 raw29592step1Labels = mixedMoment B raw29592step2 raw29592step2Labels := by
      have ha : raw29592step2 = (fun i j => raw29592step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29592step2 raw29592step1; decide +kernel
      have hl : raw29592step2Labels = raw29592step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29592step1 raw29592step1Labels permutation9 permutation7
    mixedMoment B raw29592step2 raw29592step2Labels = mixedMoment B raw29592step3 raw29592step3Labels := by
      have ha : raw29592step3 = raw29592step2 := by apply Matrix.ext; unfold raw29592step3 raw29592step2; decide +kernel
      have hl : raw29592step2Labels = labelEmbedding1 ∘ raw29592step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29592step2 raw29592step2Labels raw29592step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2604 node2604Labels := by rfl

def raw29593 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29593step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29593 raw29593Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw29593 raw29593Labels = mixedMoment B raw29593step0 raw29593step0Labels := by
      have hz : ∀ j, raw29593 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29593step0 = (fun i j => raw29593 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29593step0 raw29593; decide +kernel
      have hl : raw29593step0Labels = raw29593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29593 raw29593Labels permutation434 hz
    mixedMoment B raw29593step0 raw29593step0Labels = mixedMoment B raw29593step1 raw29593step1Labels := by
      have ha : raw29593step1 = (fun i j => raw29593step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29593step1 raw29593step0; decide +kernel
      have hl : raw29593step1Labels = raw29593step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29593step0 raw29593step0Labels permutation33 permutation7
    mixedMoment B raw29593step1 raw29593step1Labels = mixedMoment B raw29593step2 raw29593step2Labels := by
      have ha : raw29593step2 = raw29593step1 := by apply Matrix.ext; unfold raw29593step2 raw29593step1; decide +kernel
      have hl : raw29593step1Labels = labelEmbedding1 ∘ raw29593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29593step1 raw29593step1Labels raw29593step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw29594 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29594step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29594step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29594 raw29594Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw29594 raw29594Labels = mixedMoment B raw29594step0 raw29594step0Labels := by
      have hz : ∀ j, raw29594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29594step0 = (fun i j => raw29594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29594step0 raw29594; decide +kernel
      have hl : raw29594step0Labels = raw29594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29594 raw29594Labels permutation346 hz
    mixedMoment B raw29594step0 raw29594step0Labels = mixedMoment B raw29594step1 raw29594step1Labels := by
      have ha : raw29594step1 = (fun i j => raw29594step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29594step1 raw29594step0; decide +kernel
      have hl : raw29594step1Labels = raw29594step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29594step0 raw29594step0Labels permutation33 permutation7
    mixedMoment B raw29594step1 raw29594step1Labels = mixedMoment B raw29594step2 raw29594step2Labels := by
      have ha : raw29594step2 = raw29594step1 := by apply Matrix.ext; unfold raw29594step2 raw29594step1; decide +kernel
      have hl : raw29594step1Labels = labelEmbedding1 ∘ raw29594step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29594step1 raw29594step1Labels raw29594step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw29595 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29595step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-3, 1, 2], ![0, -2, 2]]
def raw29595step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29595step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29595step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29595step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29595 raw29595Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw29595 raw29595Labels = mixedMoment B raw29595step0 raw29595step0Labels := by
      have hz : ∀ j, raw29595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29595step0 = (fun i j => raw29595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29595step0 raw29595; decide +kernel
      have hl : raw29595step0Labels = raw29595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29595 raw29595Labels permutation434 hz
    mixedMoment B raw29595step0 raw29595step0Labels = mixedMoment B raw29595step1 raw29595step1Labels := by
      have hz : ∀ j, raw29595step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29595step1 = (fun i j => raw29595step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29595step1 raw29595step0; decide +kernel
      have hl : raw29595step1Labels = raw29595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29595step0 raw29595step0Labels permutation80 hz
    mixedMoment B raw29595step1 raw29595step1Labels = mixedMoment B raw29595step2 raw29595step2Labels := by
      have ha : raw29595step2 = (fun i j => raw29595step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29595step2 raw29595step1; decide +kernel
      have hl : raw29595step2Labels = raw29595step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29595step1 raw29595step1Labels permutation9 permutation7
    mixedMoment B raw29595step2 raw29595step2Labels = mixedMoment B raw29595step3 raw29595step3Labels := by
      have ha : raw29595step3 = raw29595step2 := by apply Matrix.ext; unfold raw29595step3 raw29595step2; decide +kernel
      have hl : raw29595step2Labels = labelEmbedding1 ∘ raw29595step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29595step2 raw29595step2Labels raw29595step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw29596 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29596step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29596step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29596step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29596step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29596step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29596 raw29596Labels = mixedMoment B node2523 node2523Labels := by
  calc
    mixedMoment B raw29596 raw29596Labels = mixedMoment B raw29596step0 raw29596step0Labels := by
      have hz : ∀ j, raw29596 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29596step0 = (fun i j => raw29596 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29596step0 raw29596; decide +kernel
      have hl : raw29596step0Labels = raw29596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29596 raw29596Labels permutation434 hz
    mixedMoment B raw29596step0 raw29596step0Labels = mixedMoment B raw29596step1 raw29596step1Labels := by
      have hz : ∀ j, raw29596step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29596step1 = (fun i j => raw29596step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29596step1 raw29596step0; decide +kernel
      have hl : raw29596step1Labels = raw29596step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29596step0 raw29596step0Labels permutation80 hz
    mixedMoment B raw29596step1 raw29596step1Labels = mixedMoment B raw29596step2 raw29596step2Labels := by
      have ha : raw29596step2 = (fun i j => raw29596step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29596step2 raw29596step1; decide +kernel
      have hl : raw29596step2Labels = raw29596step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29596step1 raw29596step1Labels permutation9 permutation7
    mixedMoment B raw29596step2 raw29596step2Labels = mixedMoment B raw29596step3 raw29596step3Labels := by
      have ha : raw29596step3 = raw29596step2 := by apply Matrix.ext; unfold raw29596step3 raw29596step2; decide +kernel
      have hl : raw29596step2Labels = labelEmbedding1 ∘ raw29596step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29596step2 raw29596step2Labels raw29596step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2523 node2523Labels := by rfl

def raw29597 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29597step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29597step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw29597step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29597step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw29597step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29597 raw29597Labels = mixedMoment B node3187 node3187Labels := by
  calc
    mixedMoment B raw29597 raw29597Labels = mixedMoment B raw29597step0 raw29597step0Labels := by
      have hz : ∀ j, raw29597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29597step0 = (fun i j => raw29597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29597step0 raw29597; decide +kernel
      have hl : raw29597step0Labels = raw29597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29597 raw29597Labels permutation434 hz
    mixedMoment B raw29597step0 raw29597step0Labels = mixedMoment B raw29597step1 raw29597step1Labels := by
      have hz : ∀ j, raw29597step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29597step1 = (fun i j => raw29597step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29597step1 raw29597step0; decide +kernel
      have hl : raw29597step1Labels = raw29597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29597step0 raw29597step0Labels permutation80 hz
    mixedMoment B raw29597step1 raw29597step1Labels = mixedMoment B raw29597step2 raw29597step2Labels := by
      have ha : raw29597step2 = (fun i j => raw29597step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29597step2 raw29597step1; decide +kernel
      have hl : raw29597step2Labels = raw29597step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29597step1 raw29597step1Labels permutation9 permutation7
    mixedMoment B raw29597step2 raw29597step2Labels = mixedMoment B raw29597step3 raw29597step3Labels := by
      have ha : raw29597step3 = raw29597step2 := by apply Matrix.ext; unfold raw29597step3 raw29597step2; decide +kernel
      have hl : raw29597step2Labels = labelEmbedding1 ∘ raw29597step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29597step2 raw29597step2Labels raw29597step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3187 node3187Labels := by rfl

def raw29598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29598step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29598 raw29598Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw29598 raw29598Labels = mixedMoment B raw29598step0 raw29598step0Labels := by
      have hz : ∀ j, raw29598 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29598step0 = (fun i j => raw29598 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29598step0 raw29598; decide +kernel
      have hl : raw29598step0Labels = raw29598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29598 raw29598Labels permutation434 hz
    mixedMoment B raw29598step0 raw29598step0Labels = mixedMoment B raw29598step1 raw29598step1Labels := by
      have ha : raw29598step1 = (fun i j => raw29598step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29598step1 raw29598step0; decide +kernel
      have hl : raw29598step1Labels = raw29598step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29598step0 raw29598step0Labels permutation33 permutation7
    mixedMoment B raw29598step1 raw29598step1Labels = mixedMoment B raw29598step2 raw29598step2Labels := by
      have ha : raw29598step2 = raw29598step1 := by apply Matrix.ext; unfold raw29598step2 raw29598step1; decide +kernel
      have hl : raw29598step1Labels = labelEmbedding1 ∘ raw29598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29598step1 raw29598step1Labels raw29598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2867 node2867Labels := by rfl

def raw29599 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29599step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29599step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29599 raw29599Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw29599 raw29599Labels = mixedMoment B raw29599step0 raw29599step0Labels := by
      have hz : ∀ j, raw29599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29599step0 = (fun i j => raw29599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29599step0 raw29599; decide +kernel
      have hl : raw29599step0Labels = raw29599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29599 raw29599Labels permutation346 hz
    mixedMoment B raw29599step0 raw29599step0Labels = mixedMoment B raw29599step1 raw29599step1Labels := by
      have ha : raw29599step1 = (fun i j => raw29599step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29599step1 raw29599step0; decide +kernel
      have hl : raw29599step1Labels = raw29599step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29599step0 raw29599step0Labels permutation33 permutation7
    mixedMoment B raw29599step1 raw29599step1Labels = mixedMoment B raw29599step2 raw29599step2Labels := by
      have ha : raw29599step2 = raw29599step1 := by apply Matrix.ext; unfold raw29599step2 raw29599step1; decide +kernel
      have hl : raw29599step1Labels = labelEmbedding1 ∘ raw29599step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29599step1 raw29599step1Labels raw29599step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2867 node2867Labels := by rfl

def raw29600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29600step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-3, 1, 2], ![0, -2, 2]]
def raw29600step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw29600step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29600step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw29600step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29600 raw29600Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw29600 raw29600Labels = mixedMoment B raw29600step0 raw29600step0Labels := by
      have hz : ∀ j, raw29600 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29600step0 = (fun i j => raw29600 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29600step0 raw29600; decide +kernel
      have hl : raw29600step0Labels = raw29600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29600 raw29600Labels permutation434 hz
    mixedMoment B raw29600step0 raw29600step0Labels = mixedMoment B raw29600step1 raw29600step1Labels := by
      have hz : ∀ j, raw29600step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29600step1 = (fun i j => raw29600step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29600step1 raw29600step0; decide +kernel
      have hl : raw29600step1Labels = raw29600step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29600step0 raw29600step0Labels permutation80 hz
    mixedMoment B raw29600step1 raw29600step1Labels = mixedMoment B raw29600step2 raw29600step2Labels := by
      have ha : raw29600step2 = (fun i j => raw29600step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29600step2 raw29600step1; decide +kernel
      have hl : raw29600step2Labels = raw29600step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29600step1 raw29600step1Labels permutation9 permutation7
    mixedMoment B raw29600step2 raw29600step2Labels = mixedMoment B raw29600step3 raw29600step3Labels := by
      have ha : raw29600step3 = raw29600step2 := by apply Matrix.ext; unfold raw29600step3 raw29600step2; decide +kernel
      have hl : raw29600step2Labels = labelEmbedding1 ∘ raw29600step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29600step2 raw29600step2Labels raw29600step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2888 node2888Labels := by rfl

def raw29601 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29601step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29601step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw29601step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw29601step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29601 raw29601Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw29601 raw29601Labels = mixedMoment B raw29601step0 raw29601step0Labels := by
      have hz : ∀ j, raw29601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29601step0 = (fun i j => raw29601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29601step0 raw29601; decide +kernel
      have hl : raw29601step0Labels = raw29601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29601 raw29601Labels permutation434 hz
    mixedMoment B raw29601step0 raw29601step0Labels = mixedMoment B raw29601step1 raw29601step1Labels := by
      have hz : ∀ j, raw29601step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29601step1 = (fun i j => raw29601step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29601step1 raw29601step0; decide +kernel
      have hl : raw29601step1Labels = raw29601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29601step0 raw29601step0Labels permutation80 hz
    mixedMoment B raw29601step1 raw29601step1Labels = mixedMoment B raw29601step2 raw29601step2Labels := by
      have ha : raw29601step2 = (fun i j => raw29601step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29601step2 raw29601step1; decide +kernel
      have hl : raw29601step2Labels = raw29601step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29601step1 raw29601step1Labels permutation9 permutation7
    mixedMoment B raw29601step2 raw29601step2Labels = mixedMoment B raw29601step3 raw29601step3Labels := by
      have ha : raw29601step3 = raw29601step2 := by apply Matrix.ext; unfold raw29601step3 raw29601step2; decide +kernel
      have hl : raw29601step2Labels = labelEmbedding1 ∘ raw29601step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29601step2 raw29601step2Labels raw29601step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw29602 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29602step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29602step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29602 raw29602Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw29602 raw29602Labels = mixedMoment B raw29602step0 raw29602step0Labels := by
      have hz : ∀ j, raw29602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29602step0 = (fun i j => raw29602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29602step0 raw29602; decide +kernel
      have hl : raw29602step0Labels = raw29602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29602 raw29602Labels permutation434 hz
    mixedMoment B raw29602step0 raw29602step0Labels = mixedMoment B raw29602step1 raw29602step1Labels := by
      have ha : raw29602step1 = (fun i j => raw29602step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29602step1 raw29602step0; decide +kernel
      have hl : raw29602step1Labels = raw29602step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29602step0 raw29602step0Labels permutation33 permutation7
    mixedMoment B raw29602step1 raw29602step1Labels = mixedMoment B raw29602step2 raw29602step2Labels := by
      have ha : raw29602step2 = raw29602step1 := by apply Matrix.ext; unfold raw29602step2 raw29602step1; decide +kernel
      have hl : raw29602step1Labels = labelEmbedding1 ∘ raw29602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29602step1 raw29602step1Labels raw29602step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw29603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29603step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29603 raw29603Labels = mixedMoment B node2990 node2990Labels := by
  calc
    mixedMoment B raw29603 raw29603Labels = mixedMoment B raw29603step0 raw29603step0Labels := by
      have hz : ∀ j, raw29603 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29603step0 = (fun i j => raw29603 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29603step0 raw29603; decide +kernel
      have hl : raw29603step0Labels = raw29603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29603 raw29603Labels permutation434 hz
    mixedMoment B raw29603step0 raw29603step0Labels = mixedMoment B raw29603step1 raw29603step1Labels := by
      have ha : raw29603step1 = (fun i j => raw29603step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29603step1 raw29603step0; decide +kernel
      have hl : raw29603step1Labels = raw29603step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29603step0 raw29603step0Labels permutation33 permutation7
    mixedMoment B raw29603step1 raw29603step1Labels = mixedMoment B raw29603step2 raw29603step2Labels := by
      have ha : raw29603step2 = raw29603step1 := by apply Matrix.ext; unfold raw29603step2 raw29603step1; decide +kernel
      have hl : raw29603step1Labels = labelEmbedding1 ∘ raw29603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29603step1 raw29603step1Labels raw29603step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2990 node2990Labels := by rfl

def raw29604 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29604 raw29604Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw29604 raw29604Labels = mixedMoment B raw29604step0 raw29604step0Labels := by
      have ha : raw29604step0 = (fun i j => raw29604 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29604step0 raw29604; decide +kernel
      have hl : raw29604step0Labels = raw29604Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29604 raw29604Labels permutation153 permutation7
    mixedMoment B raw29604step0 raw29604step0Labels = mixedMoment B raw29604step1 raw29604step1Labels := by
      have ha : raw29604step1 = raw29604step0 := by apply Matrix.ext; unfold raw29604step1 raw29604step0; decide +kernel
      have hl : raw29604step0Labels = labelEmbedding1 ∘ raw29604step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29604step0 raw29604step0Labels raw29604step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw29605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29605step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29605step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29605 raw29605Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw29605 raw29605Labels = mixedMoment B raw29605step0 raw29605step0Labels := by
      have hz : ∀ j, raw29605 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29605step0 = (fun i j => raw29605 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29605step0 raw29605; decide +kernel
      have hl : raw29605step0Labels = raw29605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29605 raw29605Labels permutation434 hz
    mixedMoment B raw29605step0 raw29605step0Labels = mixedMoment B raw29605step1 raw29605step1Labels := by
      have ha : raw29605step1 = (fun i j => raw29605step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29605step1 raw29605step0; decide +kernel
      have hl : raw29605step1Labels = raw29605step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29605step0 raw29605step0Labels permutation33 permutation7
    mixedMoment B raw29605step1 raw29605step1Labels = mixedMoment B raw29605step2 raw29605step2Labels := by
      have ha : raw29605step2 = raw29605step1 := by apply Matrix.ext; unfold raw29605step2 raw29605step1; decide +kernel
      have hl : raw29605step1Labels = labelEmbedding1 ∘ raw29605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29605step1 raw29605step1Labels raw29605step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw29606 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29606step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29606 raw29606Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw29606 raw29606Labels = mixedMoment B raw29606step0 raw29606step0Labels := by
      have hz : ∀ j, raw29606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29606step0 = (fun i j => raw29606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29606step0 raw29606; decide +kernel
      have hl : raw29606step0Labels = raw29606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29606 raw29606Labels permutation434 hz
    mixedMoment B raw29606step0 raw29606step0Labels = mixedMoment B raw29606step1 raw29606step1Labels := by
      have ha : raw29606step1 = (fun i j => raw29606step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29606step1 raw29606step0; decide +kernel
      have hl : raw29606step1Labels = raw29606step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29606step0 raw29606step0Labels permutation33 permutation7
    mixedMoment B raw29606step1 raw29606step1Labels = mixedMoment B raw29606step2 raw29606step2Labels := by
      have ha : raw29606step2 = raw29606step1 := by apply Matrix.ext; unfold raw29606step2 raw29606step1; decide +kernel
      have hl : raw29606step1Labels = labelEmbedding1 ∘ raw29606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29606step1 raw29606step1Labels raw29606step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw29607 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29607step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29607step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29607 raw29607Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw29607 raw29607Labels = mixedMoment B raw29607step0 raw29607step0Labels := by
      have hz : ∀ j, raw29607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29607step0 = (fun i j => raw29607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29607step0 raw29607; decide +kernel
      have hl : raw29607step0Labels = raw29607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29607 raw29607Labels permutation346 hz
    mixedMoment B raw29607step0 raw29607step0Labels = mixedMoment B raw29607step1 raw29607step1Labels := by
      have ha : raw29607step1 = (fun i j => raw29607step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29607step1 raw29607step0; decide +kernel
      have hl : raw29607step1Labels = raw29607step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29607step0 raw29607step0Labels permutation33 permutation7
    mixedMoment B raw29607step1 raw29607step1Labels = mixedMoment B raw29607step2 raw29607step2Labels := by
      have ha : raw29607step2 = raw29607step1 := by apply Matrix.ext; unfold raw29607step2 raw29607step1; decide +kernel
      have hl : raw29607step1Labels = labelEmbedding1 ∘ raw29607step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29607step1 raw29607step1Labels raw29607step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw29608 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29608step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw29608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29608 raw29608Labels = mixedMoment B node2990 node2990Labels := by
  calc
    mixedMoment B raw29608 raw29608Labels = mixedMoment B raw29608step0 raw29608step0Labels := by
      have hz : ∀ j, raw29608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29608step0 = (fun i j => raw29608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29608step0 raw29608; decide +kernel
      have hl : raw29608step0Labels = raw29608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29608 raw29608Labels permutation346 hz
    mixedMoment B raw29608step0 raw29608step0Labels = mixedMoment B raw29608step1 raw29608step1Labels := by
      have ha : raw29608step1 = (fun i j => raw29608step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29608step1 raw29608step0; decide +kernel
      have hl : raw29608step1Labels = raw29608step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29608step0 raw29608step0Labels permutation33 permutation7
    mixedMoment B raw29608step1 raw29608step1Labels = mixedMoment B raw29608step2 raw29608step2Labels := by
      have ha : raw29608step2 = raw29608step1 := by apply Matrix.ext; unfold raw29608step2 raw29608step1; decide +kernel
      have hl : raw29608step1Labels = labelEmbedding1 ∘ raw29608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29608step1 raw29608step1Labels raw29608step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2990 node2990Labels := by rfl

def raw29609 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw29609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29609 raw29609Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw29609 raw29609Labels = mixedMoment B raw29609step0 raw29609step0Labels := by
      have ha : raw29609step0 = (fun i j => raw29609 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29609step0 raw29609; decide +kernel
      have hl : raw29609step0Labels = raw29609Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29609 raw29609Labels permutation159 permutation7
    mixedMoment B raw29609step0 raw29609step0Labels = mixedMoment B raw29609step1 raw29609step1Labels := by
      have ha : raw29609step1 = raw29609step0 := by apply Matrix.ext; unfold raw29609step1 raw29609step0; decide +kernel
      have hl : raw29609step0Labels = labelEmbedding1 ∘ raw29609step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29609step0 raw29609step0Labels raw29609step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw29610 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29610step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29610 raw29610Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw29610 raw29610Labels = mixedMoment B raw29610step0 raw29610step0Labels := by
      have hz : ∀ j, raw29610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29610step0 = (fun i j => raw29610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29610step0 raw29610; decide +kernel
      have hl : raw29610step0Labels = raw29610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29610 raw29610Labels permutation346 hz
    mixedMoment B raw29610step0 raw29610step0Labels = mixedMoment B raw29610step1 raw29610step1Labels := by
      have ha : raw29610step1 = (fun i j => raw29610step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29610step1 raw29610step0; decide +kernel
      have hl : raw29610step1Labels = raw29610step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29610step0 raw29610step0Labels permutation33 permutation7
    mixedMoment B raw29610step1 raw29610step1Labels = mixedMoment B raw29610step2 raw29610step2Labels := by
      have ha : raw29610step2 = raw29610step1 := by apply Matrix.ext; unfold raw29610step2 raw29610step1; decide +kernel
      have hl : raw29610step1Labels = labelEmbedding1 ∘ raw29610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29610step1 raw29610step1Labels raw29610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw29611 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29611step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29611 raw29611Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw29611 raw29611Labels = mixedMoment B raw29611step0 raw29611step0Labels := by
      have hz : ∀ j, raw29611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29611step0 = (fun i j => raw29611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29611step0 raw29611; decide +kernel
      have hl : raw29611step0Labels = raw29611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29611 raw29611Labels permutation346 hz
    mixedMoment B raw29611step0 raw29611step0Labels = mixedMoment B raw29611step1 raw29611step1Labels := by
      have ha : raw29611step1 = (fun i j => raw29611step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29611step1 raw29611step0; decide +kernel
      have hl : raw29611step1Labels = raw29611step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29611step0 raw29611step0Labels permutation33 permutation7
    mixedMoment B raw29611step1 raw29611step1Labels = mixedMoment B raw29611step2 raw29611step2Labels := by
      have ha : raw29611step2 = raw29611step1 := by apply Matrix.ext; unfold raw29611step2 raw29611step1; decide +kernel
      have hl : raw29611step1Labels = labelEmbedding1 ∘ raw29611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29611step1 raw29611step1Labels raw29611step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw29612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29612step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw29612step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -2, 0], ![2, -1, -1]]
def raw29612step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29612step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -2, 0], ![2, -1, -1]]
def raw29612step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29612 raw29612Labels = mixedMoment B node3216 node3216Labels := by
  calc
    mixedMoment B raw29612 raw29612Labels = mixedMoment B raw29612step0 raw29612step0Labels := by
      have hz : ∀ j, raw29612 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29612step0 = (fun i j => raw29612 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29612step0 raw29612; decide +kernel
      have hl : raw29612step0Labels = raw29612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29612 raw29612Labels permutation434 hz
    mixedMoment B raw29612step0 raw29612step0Labels = mixedMoment B raw29612step1 raw29612step1Labels := by
      have hz : ∀ j, raw29612step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29612step1 = (fun i j => raw29612step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29612step1 raw29612step0; decide +kernel
      have hl : raw29612step1Labels = raw29612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29612step0 raw29612step0Labels permutation80 hz
    mixedMoment B raw29612step1 raw29612step1Labels = mixedMoment B raw29612step2 raw29612step2Labels := by
      have ha : raw29612step2 = (fun i j => raw29612step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29612step2 raw29612step1; decide +kernel
      have hl : raw29612step2Labels = raw29612step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29612step1 raw29612step1Labels permutation9 permutation7
    mixedMoment B raw29612step2 raw29612step2Labels = mixedMoment B raw29612step3 raw29612step3Labels := by
      have ha : raw29612step3 = raw29612step2 := by apply Matrix.ext; unfold raw29612step3 raw29612step2; decide +kernel
      have hl : raw29612step2Labels = labelEmbedding1 ∘ raw29612step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29612step2 raw29612step2Labels raw29612step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3216 node3216Labels := by rfl

def raw29613 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29613step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw29613step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29613step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29613step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29613step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29613 raw29613Labels = mixedMoment B node3006 node3006Labels := by
  calc
    mixedMoment B raw29613 raw29613Labels = mixedMoment B raw29613step0 raw29613step0Labels := by
      have hz : ∀ j, raw29613 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29613step0 = (fun i j => raw29613 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29613step0 raw29613; decide +kernel
      have hl : raw29613step0Labels = raw29613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29613 raw29613Labels permutation434 hz
    mixedMoment B raw29613step0 raw29613step0Labels = mixedMoment B raw29613step1 raw29613step1Labels := by
      have hz : ∀ j, raw29613step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29613step1 = (fun i j => raw29613step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29613step1 raw29613step0; decide +kernel
      have hl : raw29613step1Labels = raw29613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29613step0 raw29613step0Labels permutation80 hz
    mixedMoment B raw29613step1 raw29613step1Labels = mixedMoment B raw29613step2 raw29613step2Labels := by
      have ha : raw29613step2 = (fun i j => raw29613step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29613step2 raw29613step1; decide +kernel
      have hl : raw29613step2Labels = raw29613step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29613step1 raw29613step1Labels permutation9 permutation7
    mixedMoment B raw29613step2 raw29613step2Labels = mixedMoment B raw29613step3 raw29613step3Labels := by
      have ha : raw29613step3 = raw29613step2 := by apply Matrix.ext; unfold raw29613step3 raw29613step2; decide +kernel
      have hl : raw29613step2Labels = labelEmbedding1 ∘ raw29613step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29613step2 raw29613step2Labels raw29613step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3006 node3006Labels := by rfl

def raw29614 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29614step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29614 raw29614Labels = mixedMoment B node2943 node2943Labels := by
  calc
    mixedMoment B raw29614 raw29614Labels = mixedMoment B raw29614step0 raw29614step0Labels := by
      have hz : ∀ j, raw29614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29614step0 = (fun i j => raw29614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29614step0 raw29614; decide +kernel
      have hl : raw29614step0Labels = raw29614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29614 raw29614Labels permutation434 hz
    mixedMoment B raw29614step0 raw29614step0Labels = mixedMoment B raw29614step1 raw29614step1Labels := by
      have ha : raw29614step1 = (fun i j => raw29614step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29614step1 raw29614step0; decide +kernel
      have hl : raw29614step1Labels = raw29614step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29614step0 raw29614step0Labels permutation33 permutation7
    mixedMoment B raw29614step1 raw29614step1Labels = mixedMoment B raw29614step2 raw29614step2Labels := by
      have ha : raw29614step2 = raw29614step1 := by apply Matrix.ext; unfold raw29614step2 raw29614step1; decide +kernel
      have hl : raw29614step1Labels = labelEmbedding1 ∘ raw29614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29614step1 raw29614step1Labels raw29614step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2943 node2943Labels := by rfl

def raw29615 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw29615step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29615step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29615 raw29615Labels = mixedMoment B node2943 node2943Labels := by
  calc
    mixedMoment B raw29615 raw29615Labels = mixedMoment B raw29615step0 raw29615step0Labels := by
      have hz : ∀ j, raw29615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29615step0 = (fun i j => raw29615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29615step0 raw29615; decide +kernel
      have hl : raw29615step0Labels = raw29615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29615 raw29615Labels permutation346 hz
    mixedMoment B raw29615step0 raw29615step0Labels = mixedMoment B raw29615step1 raw29615step1Labels := by
      have ha : raw29615step1 = (fun i j => raw29615step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29615step1 raw29615step0; decide +kernel
      have hl : raw29615step1Labels = raw29615step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29615step0 raw29615step0Labels permutation33 permutation7
    mixedMoment B raw29615step1 raw29615step1Labels = mixedMoment B raw29615step2 raw29615step2Labels := by
      have ha : raw29615step2 = raw29615step1 := by apply Matrix.ext; unfold raw29615step2 raw29615step1; decide +kernel
      have hl : raw29615step1Labels = labelEmbedding1 ∘ raw29615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29615step1 raw29615step1Labels raw29615step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2943 node2943Labels := by rfl

def raw29616 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29616step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29616step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29616step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29616step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29616step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29616 raw29616Labels = mixedMoment B node2969 node2969Labels := by
  calc
    mixedMoment B raw29616 raw29616Labels = mixedMoment B raw29616step0 raw29616step0Labels := by
      have hz : ∀ j, raw29616 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29616step0 = (fun i j => raw29616 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29616step0 raw29616; decide +kernel
      have hl : raw29616step0Labels = raw29616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29616 raw29616Labels permutation434 hz
    mixedMoment B raw29616step0 raw29616step0Labels = mixedMoment B raw29616step1 raw29616step1Labels := by
      have hz : ∀ j, raw29616step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29616step1 = (fun i j => raw29616step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29616step1 raw29616step0; decide +kernel
      have hl : raw29616step1Labels = raw29616step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29616step0 raw29616step0Labels permutation80 hz
    mixedMoment B raw29616step1 raw29616step1Labels = mixedMoment B raw29616step2 raw29616step2Labels := by
      have ha : raw29616step2 = (fun i j => raw29616step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29616step2 raw29616step1; decide +kernel
      have hl : raw29616step2Labels = raw29616step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29616step1 raw29616step1Labels permutation8 permutation7
    mixedMoment B raw29616step2 raw29616step2Labels = mixedMoment B raw29616step3 raw29616step3Labels := by
      have ha : raw29616step3 = raw29616step2 := by apply Matrix.ext; unfold raw29616step3 raw29616step2; decide +kernel
      have hl : raw29616step2Labels = labelEmbedding1 ∘ raw29616step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29616step2 raw29616step2Labels raw29616step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2969 node2969Labels := by rfl

def raw29617 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29617step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 0, 2], ![1, -3, 2]]
def raw29617step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw29617step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw29617step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29617 raw29617Labels = mixedMoment B node3095 node3095Labels := by
  calc
    mixedMoment B raw29617 raw29617Labels = mixedMoment B raw29617step0 raw29617step0Labels := by
      have hz : ∀ j, raw29617 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29617step0 = (fun i j => raw29617 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29617step0 raw29617; decide +kernel
      have hl : raw29617step0Labels = raw29617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29617 raw29617Labels permutation434 hz
    mixedMoment B raw29617step0 raw29617step0Labels = mixedMoment B raw29617step1 raw29617step1Labels := by
      have hz : ∀ j, raw29617step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29617step1 = (fun i j => raw29617step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29617step1 raw29617step0; decide +kernel
      have hl : raw29617step1Labels = raw29617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29617step0 raw29617step0Labels permutation80 hz
    mixedMoment B raw29617step1 raw29617step1Labels = mixedMoment B raw29617step2 raw29617step2Labels := by
      have ha : raw29617step2 = (fun i j => raw29617step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29617step2 raw29617step1; decide +kernel
      have hl : raw29617step2Labels = raw29617step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29617step1 raw29617step1Labels permutation29 permutation5
    mixedMoment B raw29617step2 raw29617step2Labels = mixedMoment B raw29617step3 raw29617step3Labels := by
      have ha : raw29617step3 = raw29617step2 := by apply Matrix.ext; unfold raw29617step3 raw29617step2; decide +kernel
      have hl : raw29617step2Labels = labelEmbedding1 ∘ raw29617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29617step2 raw29617step2Labels raw29617step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3095 node3095Labels := by rfl

def raw29618 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29618step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 0, 2], ![1, -3, 2]]
def raw29618step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw29618step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29618step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw29618step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29618 raw29618Labels = mixedMoment B node3005 node3005Labels := by
  calc
    mixedMoment B raw29618 raw29618Labels = mixedMoment B raw29618step0 raw29618step0Labels := by
      have hz : ∀ j, raw29618 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29618step0 = (fun i j => raw29618 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29618step0 raw29618; decide +kernel
      have hl : raw29618step0Labels = raw29618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29618 raw29618Labels permutation434 hz
    mixedMoment B raw29618step0 raw29618step0Labels = mixedMoment B raw29618step1 raw29618step1Labels := by
      have hz : ∀ j, raw29618step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29618step1 = (fun i j => raw29618step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29618step1 raw29618step0; decide +kernel
      have hl : raw29618step1Labels = raw29618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29618step0 raw29618step0Labels permutation80 hz
    mixedMoment B raw29618step1 raw29618step1Labels = mixedMoment B raw29618step2 raw29618step2Labels := by
      have ha : raw29618step2 = (fun i j => raw29618step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29618step2 raw29618step1; decide +kernel
      have hl : raw29618step2Labels = raw29618step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29618step1 raw29618step1Labels permutation9 permutation7
    mixedMoment B raw29618step2 raw29618step2Labels = mixedMoment B raw29618step3 raw29618step3Labels := by
      have ha : raw29618step3 = raw29618step2 := by apply Matrix.ext; unfold raw29618step3 raw29618step2; decide +kernel
      have hl : raw29618step2Labels = labelEmbedding1 ∘ raw29618step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29618step2 raw29618step2Labels raw29618step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3005 node3005Labels := by rfl

def raw29619 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29619step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29619 raw29619Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw29619 raw29619Labels = mixedMoment B raw29619step0 raw29619step0Labels := by
      have hz : ∀ j, raw29619 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29619step0 = (fun i j => raw29619 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29619step0 raw29619; decide +kernel
      have hl : raw29619step0Labels = raw29619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29619 raw29619Labels permutation434 hz
    mixedMoment B raw29619step0 raw29619step0Labels = mixedMoment B raw29619step1 raw29619step1Labels := by
      have ha : raw29619step1 = (fun i j => raw29619step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29619step1 raw29619step0; decide +kernel
      have hl : raw29619step1Labels = raw29619step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29619step0 raw29619step0Labels permutation33 permutation7
    mixedMoment B raw29619step1 raw29619step1Labels = mixedMoment B raw29619step2 raw29619step2Labels := by
      have ha : raw29619step2 = raw29619step1 := by apply Matrix.ext; unfold raw29619step2 raw29619step1; decide +kernel
      have hl : raw29619step1Labels = labelEmbedding1 ∘ raw29619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29619step1 raw29619step1Labels raw29619step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2942 node2942Labels := by rfl

def raw29620 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw29620step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29620 raw29620Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw29620 raw29620Labels = mixedMoment B raw29620step0 raw29620step0Labels := by
      have hz : ∀ j, raw29620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29620step0 = (fun i j => raw29620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29620step0 raw29620; decide +kernel
      have hl : raw29620step0Labels = raw29620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29620 raw29620Labels permutation346 hz
    mixedMoment B raw29620step0 raw29620step0Labels = mixedMoment B raw29620step1 raw29620step1Labels := by
      have ha : raw29620step1 = (fun i j => raw29620step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29620step1 raw29620step0; decide +kernel
      have hl : raw29620step1Labels = raw29620step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29620step0 raw29620step0Labels permutation33 permutation7
    mixedMoment B raw29620step1 raw29620step1Labels = mixedMoment B raw29620step2 raw29620step2Labels := by
      have ha : raw29620step2 = raw29620step1 := by apply Matrix.ext; unfold raw29620step2 raw29620step1; decide +kernel
      have hl : raw29620step1Labels = labelEmbedding1 ∘ raw29620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29620step1 raw29620step1Labels raw29620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2942 node2942Labels := by rfl

def raw29621 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw29621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-3, 1, 2], ![1, -3, 2]]
def raw29621step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw29621step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29621step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw29621step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29621 raw29621Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw29621 raw29621Labels = mixedMoment B raw29621step0 raw29621step0Labels := by
      have hz : ∀ j, raw29621 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29621step0 = (fun i j => raw29621 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29621step0 raw29621; decide +kernel
      have hl : raw29621step0Labels = raw29621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29621 raw29621Labels permutation434 hz
    mixedMoment B raw29621step0 raw29621step0Labels = mixedMoment B raw29621step1 raw29621step1Labels := by
      have hz : ∀ j, raw29621step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29621step1 = (fun i j => raw29621step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29621step1 raw29621step0; decide +kernel
      have hl : raw29621step1Labels = raw29621step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29621step0 raw29621step0Labels permutation80 hz
    mixedMoment B raw29621step1 raw29621step1Labels = mixedMoment B raw29621step2 raw29621step2Labels := by
      have ha : raw29621step2 = (fun i j => raw29621step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29621step2 raw29621step1; decide +kernel
      have hl : raw29621step2Labels = raw29621step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29621step1 raw29621step1Labels permutation9 permutation7
    mixedMoment B raw29621step2 raw29621step2Labels = mixedMoment B raw29621step3 raw29621step3Labels := by
      have ha : raw29621step3 = raw29621step2 := by apply Matrix.ext; unfold raw29621step3 raw29621step2; decide +kernel
      have hl : raw29621step2Labels = labelEmbedding1 ∘ raw29621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29621step2 raw29621step2Labels raw29621step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2967 node2967Labels := by rfl

def raw29622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29622 raw29622Labels = mixedMoment B node5390 node5390Labels := by
  calc
    mixedMoment B raw29622 raw29622Labels = mixedMoment B raw29622step0 raw29622step0Labels := by
      have hz : ∀ j, raw29622 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29622step0 = (fun i j => raw29622 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29622step0 raw29622; decide +kernel
      have hl : raw29622step0Labels = raw29622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29622 raw29622Labels permutation434 hz
    mixedMoment B raw29622step0 raw29622step0Labels = mixedMoment B raw29622step1 raw29622step1Labels := by
      have hz : ∀ j, raw29622step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29622step1 = (fun i j => raw29622step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29622step1 raw29622step0; decide +kernel
      have hl : raw29622step1Labels = raw29622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29622step0 raw29622step0Labels permutation80 hz
    _ = mixedMoment B node5390 node5390Labels := by rfl

def raw29623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29623 raw29623Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw29623 raw29623Labels = mixedMoment B raw29623step0 raw29623step0Labels := by
      have hz : ∀ j, raw29623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29623step0 = (fun i j => raw29623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29623step0 raw29623; decide +kernel
      have hl : raw29623step0Labels = raw29623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29623 raw29623Labels permutation434 hz
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw29624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29624 raw29624Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw29624 raw29624Labels = mixedMoment B raw29624step0 raw29624step0Labels := by
      have hz : ∀ j, raw29624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29624step0 = (fun i j => raw29624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29624step0 raw29624; decide +kernel
      have hl : raw29624step0Labels = raw29624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29624 raw29624Labels permutation346 hz
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw29625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29625 raw29625Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw29625 raw29625Labels = mixedMoment B raw29625step0 raw29625step0Labels := by
      have hz : ∀ j, raw29625 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29625step0 = (fun i j => raw29625 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29625step0 raw29625; decide +kernel
      have hl : raw29625step0Labels = raw29625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29625 raw29625Labels permutation434 hz
    mixedMoment B raw29625step0 raw29625step0Labels = mixedMoment B raw29625step1 raw29625step1Labels := by
      have hz : ∀ j, raw29625step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29625step1 = (fun i j => raw29625step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29625step1 raw29625step0; decide +kernel
      have hl : raw29625step1Labels = raw29625step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29625step0 raw29625step0Labels permutation80 hz
    mixedMoment B raw29625step1 raw29625step1Labels = mixedMoment B raw29625step2 raw29625step2Labels := by
      have ha : raw29625step2 = (fun i j => raw29625step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29625step2 raw29625step1; decide +kernel
      have hl : raw29625step2Labels = raw29625step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29625step1 raw29625step1Labels permutation9 permutation2
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw29626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29626 raw29626Labels = mixedMoment B node4974 node4974Labels := by
  calc
    mixedMoment B raw29626 raw29626Labels = mixedMoment B raw29626step0 raw29626step0Labels := by
      have hz : ∀ j, raw29626 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29626step0 = (fun i j => raw29626 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29626step0 raw29626; decide +kernel
      have hl : raw29626step0Labels = raw29626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29626 raw29626Labels permutation434 hz
    _ = mixedMoment B node4974 node4974Labels := by rfl

def raw29627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29627 raw29627Labels = mixedMoment B node5115 node5115Labels := by
  calc
    mixedMoment B raw29627 raw29627Labels = mixedMoment B raw29627step0 raw29627step0Labels := by
      have ha : raw29627step0 = (fun i j => raw29627 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29627step0 raw29627; decide +kernel
      have hl : raw29627step0Labels = raw29627Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29627 raw29627Labels permutation158 permutation2
    _ = mixedMoment B node5115 node5115Labels := by rfl

def raw29628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29628 raw29628Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw29628 raw29628Labels = mixedMoment B raw29628step0 raw29628step0Labels := by
      have hz : ∀ j, raw29628 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29628step0 = (fun i j => raw29628 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29628step0 raw29628; decide +kernel
      have hl : raw29628step0Labels = raw29628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29628 raw29628Labels permutation434 hz
    mixedMoment B raw29628step0 raw29628step0Labels = mixedMoment B raw29628step1 raw29628step1Labels := by
      have ha : raw29628step1 = (fun i j => raw29628step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29628step1 raw29628step0; decide +kernel
      have hl : raw29628step1Labels = raw29628step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29628step0 raw29628step0Labels permutation33 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw29629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29629step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29629 raw29629Labels = mixedMoment B node4974 node4974Labels := by
  calc
    mixedMoment B raw29629 raw29629Labels = mixedMoment B raw29629step0 raw29629step0Labels := by
      have hz : ∀ j, raw29629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29629step0 = (fun i j => raw29629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29629step0 raw29629; decide +kernel
      have hl : raw29629step0Labels = raw29629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29629 raw29629Labels permutation346 hz
    _ = mixedMoment B node4974 node4974Labels := by rfl

def raw29630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29630 raw29630Labels = mixedMoment B node5115 node5115Labels := by
  calc
    _ = mixedMoment B node5115 node5115Labels := by rfl

def raw29631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29631 raw29631Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw29631 raw29631Labels = mixedMoment B raw29631step0 raw29631step0Labels := by
      have hz : ∀ j, raw29631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29631step0 = (fun i j => raw29631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29631step0 raw29631; decide +kernel
      have hl : raw29631step0Labels = raw29631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29631 raw29631Labels permutation346 hz
    mixedMoment B raw29631step0 raw29631step0Labels = mixedMoment B raw29631step1 raw29631step1Labels := by
      have ha : raw29631step1 = (fun i j => raw29631step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29631step1 raw29631step0; decide +kernel
      have hl : raw29631step1Labels = raw29631step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29631step0 raw29631step0Labels permutation33 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw29632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29632step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29632step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29632step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29632step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29632 raw29632Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw29632 raw29632Labels = mixedMoment B raw29632step0 raw29632step0Labels := by
      have hz : ∀ j, raw29632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29632step0 = (fun i j => raw29632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29632step0 raw29632; decide +kernel
      have hl : raw29632step0Labels = raw29632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29632 raw29632Labels permutation434 hz
    mixedMoment B raw29632step0 raw29632step0Labels = mixedMoment B raw29632step1 raw29632step1Labels := by
      have hz : ∀ j, raw29632step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29632step1 = (fun i j => raw29632step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29632step1 raw29632step0; decide +kernel
      have hl : raw29632step1Labels = raw29632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29632step0 raw29632step0Labels permutation80 hz
    mixedMoment B raw29632step1 raw29632step1Labels = mixedMoment B raw29632step2 raw29632step2Labels := by
      have ha : raw29632step2 = (fun i j => raw29632step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29632step2 raw29632step1; decide +kernel
      have hl : raw29632step2Labels = raw29632step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29632step1 raw29632step1Labels permutation25 permutation3
    mixedMoment B raw29632step2 raw29632step2Labels = mixedMoment B raw29632step3 raw29632step3Labels := by
      have ha : raw29632step3 = -raw29632step2 := by apply Matrix.ext; change ∀ i j, raw29632step3 i j = -(raw29632step2 i j); unfold raw29632step3 raw29632step2; decide +kernel
      have hl : raw29632step3Labels = raw29632step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29632step3 raw29632step3Labels = mixedMoment B raw29632step4 raw29632step4Labels := by
      have ha : raw29632step4 = raw29632step3 := by apply Matrix.ext; unfold raw29632step4 raw29632step3; decide +kernel
      have hl : raw29632step3Labels = labelEmbedding6 ∘ raw29632step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29632step3 raw29632step3Labels raw29632step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4953 node4953Labels := by rfl

def raw29633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29633step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29633step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29633step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29633step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29633 raw29633Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw29633 raw29633Labels = mixedMoment B raw29633step0 raw29633step0Labels := by
      have hz : ∀ j, raw29633 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29633step0 = (fun i j => raw29633 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29633step0 raw29633; decide +kernel
      have hl : raw29633step0Labels = raw29633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29633 raw29633Labels permutation434 hz
    mixedMoment B raw29633step0 raw29633step0Labels = mixedMoment B raw29633step1 raw29633step1Labels := by
      have ha : raw29633step1 = (fun i j => raw29633step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29633step1 raw29633step0; decide +kernel
      have hl : raw29633step1Labels = raw29633step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29633step0 raw29633step0Labels permutation125 permutation3
    mixedMoment B raw29633step1 raw29633step1Labels = mixedMoment B raw29633step2 raw29633step2Labels := by
      have ha : raw29633step2 = -raw29633step1 := by apply Matrix.ext; change ∀ i j, raw29633step2 i j = -(raw29633step1 i j); unfold raw29633step2 raw29633step1; decide +kernel
      have hl : raw29633step2Labels = raw29633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29633step2 raw29633step2Labels = mixedMoment B raw29633step3 raw29633step3Labels := by
      have ha : raw29633step3 = raw29633step2 := by apply Matrix.ext; unfold raw29633step3 raw29633step2; decide +kernel
      have hl : raw29633step2Labels = labelEmbedding6 ∘ raw29633step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29633step2 raw29633step2Labels raw29633step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4948 node4948Labels := by rfl

def raw29634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29634step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29634step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29634step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29634step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29634 raw29634Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw29634 raw29634Labels = mixedMoment B raw29634step0 raw29634step0Labels := by
      have hz : ∀ j, raw29634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29634step0 = (fun i j => raw29634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29634step0 raw29634; decide +kernel
      have hl : raw29634step0Labels = raw29634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29634 raw29634Labels permutation346 hz
    mixedMoment B raw29634step0 raw29634step0Labels = mixedMoment B raw29634step1 raw29634step1Labels := by
      have ha : raw29634step1 = (fun i j => raw29634step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29634step1 raw29634step0; decide +kernel
      have hl : raw29634step1Labels = raw29634step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29634step0 raw29634step0Labels permutation125 permutation3
    mixedMoment B raw29634step1 raw29634step1Labels = mixedMoment B raw29634step2 raw29634step2Labels := by
      have ha : raw29634step2 = -raw29634step1 := by apply Matrix.ext; change ∀ i j, raw29634step2 i j = -(raw29634step1 i j); unfold raw29634step2 raw29634step1; decide +kernel
      have hl : raw29634step2Labels = raw29634step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29634step2 raw29634step2Labels = mixedMoment B raw29634step3 raw29634step3Labels := by
      have ha : raw29634step3 = raw29634step2 := by apply Matrix.ext; unfold raw29634step3 raw29634step2; decide +kernel
      have hl : raw29634step2Labels = labelEmbedding6 ∘ raw29634step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29634step2 raw29634step2Labels raw29634step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4948 node4948Labels := by rfl

def raw29635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29635step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29635 raw29635Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw29635 raw29635Labels = mixedMoment B raw29635step0 raw29635step0Labels := by
      have hz : ∀ j, raw29635 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29635step0 = (fun i j => raw29635 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29635step0 raw29635; decide +kernel
      have hl : raw29635step0Labels = raw29635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29635 raw29635Labels permutation434 hz
    mixedMoment B raw29635step0 raw29635step0Labels = mixedMoment B raw29635step1 raw29635step1Labels := by
      have hz : ∀ j, raw29635step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29635step1 = (fun i j => raw29635step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29635step1 raw29635step0; decide +kernel
      have hl : raw29635step1Labels = raw29635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29635step0 raw29635step0Labels permutation80 hz
    mixedMoment B raw29635step1 raw29635step1Labels = mixedMoment B raw29635step2 raw29635step2Labels := by
      have ha : raw29635step2 = (fun i j => raw29635step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29635step2 raw29635step1; decide +kernel
      have hl : raw29635step2Labels = raw29635step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29635step1 raw29635step1Labels permutation9 permutation2
    _ = mixedMoment B node5174 node5174Labels := by rfl

def raw29636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29636step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29636 raw29636Labels = mixedMoment B node3741 node3741Labels := by
  calc
    mixedMoment B raw29636 raw29636Labels = mixedMoment B raw29636step0 raw29636step0Labels := by
      have hz : ∀ j, raw29636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29636step0 = (fun i j => raw29636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29636step0 raw29636; decide +kernel
      have hl : raw29636step0Labels = raw29636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29636 raw29636Labels permutation434 hz
    mixedMoment B raw29636step0 raw29636step0Labels = mixedMoment B raw29636step1 raw29636step1Labels := by
      have hz : ∀ j, raw29636step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29636step1 = (fun i j => raw29636step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29636step1 raw29636step0; decide +kernel
      have hl : raw29636step1Labels = raw29636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29636step0 raw29636step0Labels permutation80 hz
    mixedMoment B raw29636step1 raw29636step1Labels = mixedMoment B raw29636step2 raw29636step2Labels := by
      have ha : raw29636step2 = (fun i j => raw29636step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29636step2 raw29636step1; decide +kernel
      have hl : raw29636step2Labels = raw29636step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29636step1 raw29636step1Labels permutation14 permutation3
    _ = mixedMoment B node3741 node3741Labels := by rfl

def raw29637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29637 raw29637Labels = mixedMoment B node3933 node3933Labels := by
  calc
    mixedMoment B raw29637 raw29637Labels = mixedMoment B raw29637step0 raw29637step0Labels := by
      have hz : ∀ j, raw29637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29637step0 = (fun i j => raw29637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29637step0 raw29637; decide +kernel
      have hl : raw29637step0Labels = raw29637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29637 raw29637Labels permutation434 hz
    mixedMoment B raw29637step0 raw29637step0Labels = mixedMoment B raw29637step1 raw29637step1Labels := by
      have ha : raw29637step1 = (fun i j => raw29637step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29637step1 raw29637step0; decide +kernel
      have hl : raw29637step1Labels = raw29637step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29637step0 raw29637step0Labels permutation125 permutation3
    mixedMoment B raw29637step1 raw29637step1Labels = mixedMoment B raw29637step2 raw29637step2Labels := by
      have ha : raw29637step2 = -raw29637step1 := by apply Matrix.ext; change ∀ i j, raw29637step2 i j = -(raw29637step1 i j); unfold raw29637step2 raw29637step1; decide +kernel
      have hl : raw29637step2Labels = raw29637step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3933 node3933Labels := by rfl

def raw29638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29638 raw29638Labels = mixedMoment B node3933 node3933Labels := by
  calc
    mixedMoment B raw29638 raw29638Labels = mixedMoment B raw29638step0 raw29638step0Labels := by
      have hz : ∀ j, raw29638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29638step0 = (fun i j => raw29638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29638step0 raw29638; decide +kernel
      have hl : raw29638step0Labels = raw29638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29638 raw29638Labels permutation346 hz
    mixedMoment B raw29638step0 raw29638step0Labels = mixedMoment B raw29638step1 raw29638step1Labels := by
      have ha : raw29638step1 = (fun i j => raw29638step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29638step1 raw29638step0; decide +kernel
      have hl : raw29638step1Labels = raw29638step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29638step0 raw29638step0Labels permutation125 permutation3
    mixedMoment B raw29638step1 raw29638step1Labels = mixedMoment B raw29638step2 raw29638step2Labels := by
      have ha : raw29638step2 = -raw29638step1 := by apply Matrix.ext; change ∀ i j, raw29638step2 i j = -(raw29638step1 i j); unfold raw29638step2 raw29638step1; decide +kernel
      have hl : raw29638step2Labels = raw29638step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3933 node3933Labels := by rfl

def raw29639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29639step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw29639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29639step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29639step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29639 raw29639Labels = mixedMoment B node4001 node4001Labels := by
  calc
    mixedMoment B raw29639 raw29639Labels = mixedMoment B raw29639step0 raw29639step0Labels := by
      have hz : ∀ j, raw29639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29639step0 = (fun i j => raw29639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29639step0 raw29639; decide +kernel
      have hl : raw29639step0Labels = raw29639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29639 raw29639Labels permutation434 hz
    mixedMoment B raw29639step0 raw29639step0Labels = mixedMoment B raw29639step1 raw29639step1Labels := by
      have hz : ∀ j, raw29639step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29639step1 = (fun i j => raw29639step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29639step1 raw29639step0; decide +kernel
      have hl : raw29639step1Labels = raw29639step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29639step0 raw29639step0Labels permutation80 hz
    mixedMoment B raw29639step1 raw29639step1Labels = mixedMoment B raw29639step2 raw29639step2Labels := by
      have ha : raw29639step2 = (fun i j => raw29639step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29639step2 raw29639step1; decide +kernel
      have hl : raw29639step2Labels = raw29639step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29639step1 raw29639step1Labels permutation25 permutation3
    mixedMoment B raw29639step2 raw29639step2Labels = mixedMoment B raw29639step3 raw29639step3Labels := by
      have ha : raw29639step3 = -raw29639step2 := by apply Matrix.ext; change ∀ i j, raw29639step3 i j = -(raw29639step2 i j); unfold raw29639step3 raw29639step2; decide +kernel
      have hl : raw29639step3Labels = raw29639step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4001 node4001Labels := by rfl

def raw29640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29640 raw29640Labels = mixedMoment B node2818 node2818Labels := by
  calc
    mixedMoment B raw29640 raw29640Labels = mixedMoment B raw29640step0 raw29640step0Labels := by
      have hz : ∀ j, raw29640 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29640step0 = (fun i j => raw29640 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29640step0 raw29640; decide +kernel
      have hl : raw29640step0Labels = raw29640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29640 raw29640Labels permutation434 hz
    mixedMoment B raw29640step0 raw29640step0Labels = mixedMoment B raw29640step1 raw29640step1Labels := by
      have ha : raw29640step1 = (fun i j => raw29640step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29640step1 raw29640step0; decide +kernel
      have hl : raw29640step1Labels = raw29640step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29640step0 raw29640step0Labels permutation32 permutation3
    _ = mixedMoment B node2818 node2818Labels := by rfl

def raw29641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29641 raw29641Labels = mixedMoment B node2897 node2897Labels := by
  calc
    mixedMoment B raw29641 raw29641Labels = mixedMoment B raw29641step0 raw29641step0Labels := by
      have ha : raw29641step0 = (fun i j => raw29641 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29641step0 raw29641; decide +kernel
      have hl : raw29641step0Labels = raw29641Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29641 raw29641Labels permutation158 permutation3
    _ = mixedMoment B node2897 node2897Labels := by rfl

def raw29642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29642 raw29642Labels = mixedMoment B node2960 node2960Labels := by
  calc
    mixedMoment B raw29642 raw29642Labels = mixedMoment B raw29642step0 raw29642step0Labels := by
      have hz : ∀ j, raw29642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29642step0 = (fun i j => raw29642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29642step0 raw29642; decide +kernel
      have hl : raw29642step0Labels = raw29642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29642 raw29642Labels permutation434 hz
    mixedMoment B raw29642step0 raw29642step0Labels = mixedMoment B raw29642step1 raw29642step1Labels := by
      have ha : raw29642step1 = (fun i j => raw29642step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29642step1 raw29642step0; decide +kernel
      have hl : raw29642step1Labels = raw29642step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29642step0 raw29642step0Labels permutation36 permutation3
    _ = mixedMoment B node2960 node2960Labels := by rfl

def raw29643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29643 raw29643Labels = mixedMoment B node2818 node2818Labels := by
  calc
    mixedMoment B raw29643 raw29643Labels = mixedMoment B raw29643step0 raw29643step0Labels := by
      have hz : ∀ j, raw29643 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29643step0 = (fun i j => raw29643 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29643step0 raw29643; decide +kernel
      have hl : raw29643step0Labels = raw29643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29643 raw29643Labels permutation346 hz
    mixedMoment B raw29643step0 raw29643step0Labels = mixedMoment B raw29643step1 raw29643step1Labels := by
      have ha : raw29643step1 = (fun i j => raw29643step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29643step1 raw29643step0; decide +kernel
      have hl : raw29643step1Labels = raw29643step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29643step0 raw29643step0Labels permutation32 permutation3
    _ = mixedMoment B node2818 node2818Labels := by rfl

def raw29644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29644 raw29644Labels = mixedMoment B node2897 node2897Labels := by
  calc
    mixedMoment B raw29644 raw29644Labels = mixedMoment B raw29644step0 raw29644step0Labels := by
      have ha : raw29644step0 = (fun i j => raw29644 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29644step0 raw29644; decide +kernel
      have hl : raw29644step0Labels = raw29644Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29644 raw29644Labels permutation152 permutation3
    _ = mixedMoment B node2897 node2897Labels := by rfl

def raw29645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29645 raw29645Labels = mixedMoment B node2960 node2960Labels := by
  calc
    mixedMoment B raw29645 raw29645Labels = mixedMoment B raw29645step0 raw29645step0Labels := by
      have hz : ∀ j, raw29645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29645step0 = (fun i j => raw29645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29645step0 raw29645; decide +kernel
      have hl : raw29645step0Labels = raw29645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29645 raw29645Labels permutation346 hz
    mixedMoment B raw29645step0 raw29645step0Labels = mixedMoment B raw29645step1 raw29645step1Labels := by
      have ha : raw29645step1 = (fun i j => raw29645step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29645step1 raw29645step0; decide +kernel
      have hl : raw29645step1Labels = raw29645step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29645step0 raw29645step0Labels permutation36 permutation3
    _ = mixedMoment B node2960 node2960Labels := by rfl

def raw29646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29646step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29646step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29646 raw29646Labels = mixedMoment B node2345 node2345Labels := by
  calc
    mixedMoment B raw29646 raw29646Labels = mixedMoment B raw29646step0 raw29646step0Labels := by
      have hz : ∀ j, raw29646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29646step0 = (fun i j => raw29646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29646step0 raw29646; decide +kernel
      have hl : raw29646step0Labels = raw29646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29646 raw29646Labels permutation434 hz
    mixedMoment B raw29646step0 raw29646step0Labels = mixedMoment B raw29646step1 raw29646step1Labels := by
      have hz : ∀ j, raw29646step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29646step1 = (fun i j => raw29646step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29646step1 raw29646step0; decide +kernel
      have hl : raw29646step1Labels = raw29646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29646step0 raw29646step0Labels permutation80 hz
    mixedMoment B raw29646step1 raw29646step1Labels = mixedMoment B raw29646step2 raw29646step2Labels := by
      have ha : raw29646step2 = (fun i j => raw29646step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29646step2 raw29646step1; decide +kernel
      have hl : raw29646step2Labels = raw29646step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29646step1 raw29646step1Labels permutation25 permutation3
    mixedMoment B raw29646step2 raw29646step2Labels = mixedMoment B raw29646step3 raw29646step3Labels := by
      have ha : raw29646step3 = -raw29646step2 := by apply Matrix.ext; change ∀ i j, raw29646step3 i j = -(raw29646step2 i j); unfold raw29646step3 raw29646step2; decide +kernel
      have hl : raw29646step3Labels = raw29646step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2345 node2345Labels := by rfl

def raw29647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29647 raw29647Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw29647 raw29647Labels = mixedMoment B raw29647step0 raw29647step0Labels := by
      have hz : ∀ j, raw29647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29647step0 = (fun i j => raw29647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29647step0 raw29647; decide +kernel
      have hl : raw29647step0Labels = raw29647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29647 raw29647Labels permutation434 hz
    mixedMoment B raw29647step0 raw29647step0Labels = mixedMoment B raw29647step1 raw29647step1Labels := by
      have ha : raw29647step1 = (fun i j => raw29647step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29647step1 raw29647step0; decide +kernel
      have hl : raw29647step1Labels = raw29647step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29647step0 raw29647step0Labels permutation125 permutation3
    mixedMoment B raw29647step1 raw29647step1Labels = mixedMoment B raw29647step2 raw29647step2Labels := by
      have ha : raw29647step2 = -raw29647step1 := by apply Matrix.ext; change ∀ i j, raw29647step2 i j = -(raw29647step1 i j); unfold raw29647step2 raw29647step1; decide +kernel
      have hl : raw29647step2Labels = raw29647step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2339 node2339Labels := by rfl

def raw29648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29648 raw29648Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw29648 raw29648Labels = mixedMoment B raw29648step0 raw29648step0Labels := by
      have hz : ∀ j, raw29648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29648step0 = (fun i j => raw29648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29648step0 raw29648; decide +kernel
      have hl : raw29648step0Labels = raw29648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29648 raw29648Labels permutation346 hz
    mixedMoment B raw29648step0 raw29648step0Labels = mixedMoment B raw29648step1 raw29648step1Labels := by
      have ha : raw29648step1 = (fun i j => raw29648step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29648step1 raw29648step0; decide +kernel
      have hl : raw29648step1Labels = raw29648step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29648step0 raw29648step0Labels permutation125 permutation3
    mixedMoment B raw29648step1 raw29648step1Labels = mixedMoment B raw29648step2 raw29648step2Labels := by
      have ha : raw29648step2 = -raw29648step1 := by apply Matrix.ext; change ∀ i j, raw29648step2 i j = -(raw29648step1 i j); unfold raw29648step2 raw29648step1; decide +kernel
      have hl : raw29648step2Labels = raw29648step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2339 node2339Labels := by rfl

def raw29649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29649step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29649step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29649step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29649 raw29649Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw29649 raw29649Labels = mixedMoment B raw29649step0 raw29649step0Labels := by
      have hz : ∀ j, raw29649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29649step0 = (fun i j => raw29649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29649step0 raw29649; decide +kernel
      have hl : raw29649step0Labels = raw29649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29649 raw29649Labels permutation434 hz
    mixedMoment B raw29649step0 raw29649step0Labels = mixedMoment B raw29649step1 raw29649step1Labels := by
      have hz : ∀ j, raw29649step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29649step1 = (fun i j => raw29649step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29649step1 raw29649step0; decide +kernel
      have hl : raw29649step1Labels = raw29649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29649step0 raw29649step0Labels permutation80 hz
    mixedMoment B raw29649step1 raw29649step1Labels = mixedMoment B raw29649step2 raw29649step2Labels := by
      have ha : raw29649step2 = (fun i j => raw29649step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29649step2 raw29649step1; decide +kernel
      have hl : raw29649step2Labels = raw29649step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29649step1 raw29649step1Labels permutation25 permutation3
    mixedMoment B raw29649step2 raw29649step2Labels = mixedMoment B raw29649step3 raw29649step3Labels := by
      have ha : raw29649step3 = -raw29649step2 := by apply Matrix.ext; change ∀ i j, raw29649step3 i j = -(raw29649step2 i j); unfold raw29649step3 raw29649step2; decide +kernel
      have hl : raw29649step3Labels = raw29649step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw29650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29650step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29650step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29650 raw29650Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw29650 raw29650Labels = mixedMoment B raw29650step0 raw29650step0Labels := by
      have hz : ∀ j, raw29650 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29650step0 = (fun i j => raw29650 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29650step0 raw29650; decide +kernel
      have hl : raw29650step0Labels = raw29650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29650 raw29650Labels permutation434 hz
    mixedMoment B raw29650step0 raw29650step0Labels = mixedMoment B raw29650step1 raw29650step1Labels := by
      have ha : raw29650step1 = (fun i j => raw29650step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29650step1 raw29650step0; decide +kernel
      have hl : raw29650step1Labels = raw29650step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29650step0 raw29650step0Labels permutation32 permutation3
    mixedMoment B raw29650step1 raw29650step1Labels = mixedMoment B raw29650step2 raw29650step2Labels := by
      have ha : raw29650step2 = raw29650step1 := by apply Matrix.ext; unfold raw29650step2 raw29650step1; decide +kernel
      have hl : raw29650step1Labels = labelEmbedding6 ∘ raw29650step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29650step1 raw29650step1Labels raw29650step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw29651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29651step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29651 raw29651Labels = mixedMoment B node5039 node5039Labels := by
  calc
    mixedMoment B raw29651 raw29651Labels = mixedMoment B raw29651step0 raw29651step0Labels := by
      have ha : raw29651step0 = (fun i j => raw29651 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29651step0 raw29651; decide +kernel
      have hl : raw29651step0Labels = raw29651Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29651 raw29651Labels permutation200 permutation3
    mixedMoment B raw29651step0 raw29651step0Labels = mixedMoment B raw29651step1 raw29651step1Labels := by
      have ha : raw29651step1 = raw29651step0 := by apply Matrix.ext; unfold raw29651step1 raw29651step0; decide +kernel
      have hl : raw29651step0Labels = labelEmbedding6 ∘ raw29651step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29651step0 raw29651step0Labels raw29651step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5039 node5039Labels := by rfl

def raw29652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29652step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29652step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29652 raw29652Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw29652 raw29652Labels = mixedMoment B raw29652step0 raw29652step0Labels := by
      have hz : ∀ j, raw29652 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29652step0 = (fun i j => raw29652 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29652step0 raw29652; decide +kernel
      have hl : raw29652step0Labels = raw29652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29652 raw29652Labels permutation434 hz
    mixedMoment B raw29652step0 raw29652step0Labels = mixedMoment B raw29652step1 raw29652step1Labels := by
      have ha : raw29652step1 = (fun i j => raw29652step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29652step1 raw29652step0; decide +kernel
      have hl : raw29652step1Labels = raw29652step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29652step0 raw29652step0Labels permutation36 permutation3
    mixedMoment B raw29652step1 raw29652step1Labels = mixedMoment B raw29652step2 raw29652step2Labels := by
      have ha : raw29652step2 = raw29652step1 := by apply Matrix.ext; unfold raw29652step2 raw29652step1; decide +kernel
      have hl : raw29652step1Labels = labelEmbedding6 ∘ raw29652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29652step1 raw29652step1Labels raw29652step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw29653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29653step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29653 raw29653Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw29653 raw29653Labels = mixedMoment B raw29653step0 raw29653step0Labels := by
      have hz : ∀ j, raw29653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29653step0 = (fun i j => raw29653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29653step0 raw29653; decide +kernel
      have hl : raw29653step0Labels = raw29653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29653 raw29653Labels permutation346 hz
    mixedMoment B raw29653step0 raw29653step0Labels = mixedMoment B raw29653step1 raw29653step1Labels := by
      have ha : raw29653step1 = (fun i j => raw29653step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29653step1 raw29653step0; decide +kernel
      have hl : raw29653step1Labels = raw29653step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29653step0 raw29653step0Labels permutation32 permutation3
    mixedMoment B raw29653step1 raw29653step1Labels = mixedMoment B raw29653step2 raw29653step2Labels := by
      have ha : raw29653step2 = raw29653step1 := by apply Matrix.ext; unfold raw29653step2 raw29653step1; decide +kernel
      have hl : raw29653step1Labels = labelEmbedding6 ∘ raw29653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29653step1 raw29653step1Labels raw29653step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw29654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29654step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29654 raw29654Labels = mixedMoment B node5039 node5039Labels := by
  calc
    mixedMoment B raw29654 raw29654Labels = mixedMoment B raw29654step0 raw29654step0Labels := by
      have ha : raw29654step0 = (fun i j => raw29654 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29654step0 raw29654; decide +kernel
      have hl : raw29654step0Labels = raw29654Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29654 raw29654Labels permutation176 permutation3
    mixedMoment B raw29654step0 raw29654step0Labels = mixedMoment B raw29654step1 raw29654step1Labels := by
      have ha : raw29654step1 = raw29654step0 := by apply Matrix.ext; unfold raw29654step1 raw29654step0; decide +kernel
      have hl : raw29654step0Labels = labelEmbedding6 ∘ raw29654step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29654step0 raw29654step0Labels raw29654step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5039 node5039Labels := by rfl

def raw29655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29655step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29655 raw29655Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw29655 raw29655Labels = mixedMoment B raw29655step0 raw29655step0Labels := by
      have hz : ∀ j, raw29655 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29655step0 = (fun i j => raw29655 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29655step0 raw29655; decide +kernel
      have hl : raw29655step0Labels = raw29655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29655 raw29655Labels permutation346 hz
    mixedMoment B raw29655step0 raw29655step0Labels = mixedMoment B raw29655step1 raw29655step1Labels := by
      have ha : raw29655step1 = (fun i j => raw29655step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29655step1 raw29655step0; decide +kernel
      have hl : raw29655step1Labels = raw29655step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29655step0 raw29655step0Labels permutation36 permutation3
    mixedMoment B raw29655step1 raw29655step1Labels = mixedMoment B raw29655step2 raw29655step2Labels := by
      have ha : raw29655step2 = raw29655step1 := by apply Matrix.ext; unfold raw29655step2 raw29655step1; decide +kernel
      have hl : raw29655step1Labels = labelEmbedding6 ∘ raw29655step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29655step1 raw29655step1Labels raw29655step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw29656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw29656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw29656step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw29656step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29656 raw29656Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw29656 raw29656Labels = mixedMoment B raw29656step0 raw29656step0Labels := by
      have hz : ∀ j, raw29656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29656step0 = (fun i j => raw29656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29656step0 raw29656; decide +kernel
      have hl : raw29656step0Labels = raw29656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29656 raw29656Labels permutation434 hz
    mixedMoment B raw29656step0 raw29656step0Labels = mixedMoment B raw29656step1 raw29656step1Labels := by
      have hz : ∀ j, raw29656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29656step1 = (fun i j => raw29656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29656step1 raw29656step0; decide +kernel
      have hl : raw29656step1Labels = raw29656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29656step0 raw29656step0Labels permutation80 hz
    mixedMoment B raw29656step1 raw29656step1Labels = mixedMoment B raw29656step2 raw29656step2Labels := by
      have ha : raw29656step2 = (fun i j => raw29656step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29656step2 raw29656step1; decide +kernel
      have hl : raw29656step2Labels = raw29656step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29656step1 raw29656step1Labels permutation9 permutation3
    mixedMoment B raw29656step2 raw29656step2Labels = mixedMoment B raw29656step3 raw29656step3Labels := by
      have ha : raw29656step3 = raw29656step2 := by apply Matrix.ext; unfold raw29656step3 raw29656step2; decide +kernel
      have hl : raw29656step2Labels = labelEmbedding6 ∘ raw29656step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29656step2 raw29656step2Labels raw29656step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4952 node4952Labels := by rfl

def raw29657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29657step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29657step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29657step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29657step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29657 raw29657Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw29657 raw29657Labels = mixedMoment B raw29657step0 raw29657step0Labels := by
      have hz : ∀ j, raw29657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29657step0 = (fun i j => raw29657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29657step0 raw29657; decide +kernel
      have hl : raw29657step0Labels = raw29657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29657 raw29657Labels permutation434 hz
    mixedMoment B raw29657step0 raw29657step0Labels = mixedMoment B raw29657step1 raw29657step1Labels := by
      have ha : raw29657step1 = (fun i j => raw29657step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29657step1 raw29657step0; decide +kernel
      have hl : raw29657step1Labels = raw29657step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29657step0 raw29657step0Labels permutation125 permutation3
    mixedMoment B raw29657step1 raw29657step1Labels = mixedMoment B raw29657step2 raw29657step2Labels := by
      have ha : raw29657step2 = -raw29657step1 := by apply Matrix.ext; change ∀ i j, raw29657step2 i j = -(raw29657step1 i j); unfold raw29657step2 raw29657step1; decide +kernel
      have hl : raw29657step2Labels = raw29657step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29657step2 raw29657step2Labels = mixedMoment B raw29657step3 raw29657step3Labels := by
      have ha : raw29657step3 = raw29657step2 := by apply Matrix.ext; unfold raw29657step3 raw29657step2; decide +kernel
      have hl : raw29657step2Labels = labelEmbedding6 ∘ raw29657step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29657step2 raw29657step2Labels raw29657step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw29658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29658step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29658step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29658step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29658step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29658 raw29658Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw29658 raw29658Labels = mixedMoment B raw29658step0 raw29658step0Labels := by
      have hz : ∀ j, raw29658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29658step0 = (fun i j => raw29658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29658step0 raw29658; decide +kernel
      have hl : raw29658step0Labels = raw29658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29658 raw29658Labels permutation346 hz
    mixedMoment B raw29658step0 raw29658step0Labels = mixedMoment B raw29658step1 raw29658step1Labels := by
      have ha : raw29658step1 = (fun i j => raw29658step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29658step1 raw29658step0; decide +kernel
      have hl : raw29658step1Labels = raw29658step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29658step0 raw29658step0Labels permutation125 permutation3
    mixedMoment B raw29658step1 raw29658step1Labels = mixedMoment B raw29658step2 raw29658step2Labels := by
      have ha : raw29658step2 = -raw29658step1 := by apply Matrix.ext; change ∀ i j, raw29658step2 i j = -(raw29658step1 i j); unfold raw29658step2 raw29658step1; decide +kernel
      have hl : raw29658step2Labels = raw29658step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29658step2 raw29658step2Labels = mixedMoment B raw29658step3 raw29658step3Labels := by
      have ha : raw29658step3 = raw29658step2 := by apply Matrix.ext; unfold raw29658step3 raw29658step2; decide +kernel
      have hl : raw29658step2Labels = labelEmbedding6 ∘ raw29658step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29658step2 raw29658step2Labels raw29658step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw29659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![3, -2, -1], ![1, 0, -1]]
def raw29659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29659step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29659step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29659 raw29659Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw29659 raw29659Labels = mixedMoment B raw29659step0 raw29659step0Labels := by
      have hz : ∀ j, raw29659 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29659step0 = (fun i j => raw29659 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29659step0 raw29659; decide +kernel
      have hl : raw29659step0Labels = raw29659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29659 raw29659Labels permutation434 hz
    mixedMoment B raw29659step0 raw29659step0Labels = mixedMoment B raw29659step1 raw29659step1Labels := by
      have hz : ∀ j, raw29659step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29659step1 = (fun i j => raw29659step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29659step1 raw29659step0; decide +kernel
      have hl : raw29659step1Labels = raw29659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29659step0 raw29659step0Labels permutation80 hz
    mixedMoment B raw29659step1 raw29659step1Labels = mixedMoment B raw29659step2 raw29659step2Labels := by
      have ha : raw29659step2 = (fun i j => raw29659step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29659step2 raw29659step1; decide +kernel
      have hl : raw29659step2Labels = raw29659step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29659step1 raw29659step1Labels permutation9 permutation3
    mixedMoment B raw29659step2 raw29659step2Labels = mixedMoment B raw29659step3 raw29659step3Labels := by
      have ha : raw29659step3 = raw29659step2 := by apply Matrix.ext; unfold raw29659step3 raw29659step2; decide +kernel
      have hl : raw29659step2Labels = labelEmbedding6 ∘ raw29659step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29659step2 raw29659step2Labels raw29659step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw29660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29660step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29660 raw29660Labels = mixedMoment B node3934 node3934Labels := by
  calc
    mixedMoment B raw29660 raw29660Labels = mixedMoment B raw29660step0 raw29660step0Labels := by
      have hz : ∀ j, raw29660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29660step0 = (fun i j => raw29660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29660step0 raw29660; decide +kernel
      have hl : raw29660step0Labels = raw29660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29660 raw29660Labels permutation434 hz
    mixedMoment B raw29660step0 raw29660step0Labels = mixedMoment B raw29660step1 raw29660step1Labels := by
      have hz : ∀ j, raw29660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29660step1 = (fun i j => raw29660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29660step1 raw29660step0; decide +kernel
      have hl : raw29660step1Labels = raw29660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29660step0 raw29660step0Labels permutation80 hz
    mixedMoment B raw29660step1 raw29660step1Labels = mixedMoment B raw29660step2 raw29660step2Labels := by
      have ha : raw29660step2 = (fun i j => raw29660step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29660step2 raw29660step1; decide +kernel
      have hl : raw29660step2Labels = raw29660step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29660step1 raw29660step1Labels permutation8 permutation3
    _ = mixedMoment B node3934 node3934Labels := by rfl

def raw29661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29661 raw29661Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw29661 raw29661Labels = mixedMoment B raw29661step0 raw29661step0Labels := by
      have hz : ∀ j, raw29661 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29661step0 = (fun i j => raw29661 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29661step0 raw29661; decide +kernel
      have hl : raw29661step0Labels = raw29661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29661 raw29661Labels permutation434 hz
    mixedMoment B raw29661step0 raw29661step0Labels = mixedMoment B raw29661step1 raw29661step1Labels := by
      have ha : raw29661step1 = (fun i j => raw29661step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29661step1 raw29661step0; decide +kernel
      have hl : raw29661step1Labels = raw29661step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29661step0 raw29661step0Labels permutation125 permutation3
    mixedMoment B raw29661step1 raw29661step1Labels = mixedMoment B raw29661step2 raw29661step2Labels := by
      have ha : raw29661step2 = -raw29661step1 := by apply Matrix.ext; change ∀ i j, raw29661step2 i j = -(raw29661step1 i j); unfold raw29661step2 raw29661step1; decide +kernel
      have hl : raw29661step2Labels = raw29661step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw29662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29662 raw29662Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw29662 raw29662Labels = mixedMoment B raw29662step0 raw29662step0Labels := by
      have hz : ∀ j, raw29662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29662step0 = (fun i j => raw29662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29662step0 raw29662; decide +kernel
      have hl : raw29662step0Labels = raw29662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29662 raw29662Labels permutation346 hz
    mixedMoment B raw29662step0 raw29662step0Labels = mixedMoment B raw29662step1 raw29662step1Labels := by
      have ha : raw29662step1 = (fun i j => raw29662step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29662step1 raw29662step0; decide +kernel
      have hl : raw29662step1Labels = raw29662step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29662step0 raw29662step0Labels permutation125 permutation3
    mixedMoment B raw29662step1 raw29662step1Labels = mixedMoment B raw29662step2 raw29662step2Labels := by
      have ha : raw29662step2 = -raw29662step1 := by apply Matrix.ext; change ∀ i j, raw29662step2 i j = -(raw29662step1 i j); unfold raw29662step2 raw29662step1; decide +kernel
      have hl : raw29662step2Labels = raw29662step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw29663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw29663step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw29663step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29663 raw29663Labels = mixedMoment B node4000 node4000Labels := by
  calc
    mixedMoment B raw29663 raw29663Labels = mixedMoment B raw29663step0 raw29663step0Labels := by
      have hz : ∀ j, raw29663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29663step0 = (fun i j => raw29663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29663step0 raw29663; decide +kernel
      have hl : raw29663step0Labels = raw29663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29663 raw29663Labels permutation434 hz
    mixedMoment B raw29663step0 raw29663step0Labels = mixedMoment B raw29663step1 raw29663step1Labels := by
      have hz : ∀ j, raw29663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29663step1 = (fun i j => raw29663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29663step1 raw29663step0; decide +kernel
      have hl : raw29663step1Labels = raw29663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29663step0 raw29663step0Labels permutation80 hz
    mixedMoment B raw29663step1 raw29663step1Labels = mixedMoment B raw29663step2 raw29663step2Labels := by
      have ha : raw29663step2 = (fun i j => raw29663step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29663step2 raw29663step1; decide +kernel
      have hl : raw29663step2Labels = raw29663step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29663step1 raw29663step1Labels permutation9 permutation3
    _ = mixedMoment B node4000 node4000Labels := by rfl

def raw29664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29664 raw29664Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw29664 raw29664Labels = mixedMoment B raw29664step0 raw29664step0Labels := by
      have hz : ∀ j, raw29664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29664step0 = (fun i j => raw29664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29664step0 raw29664; decide +kernel
      have hl : raw29664step0Labels = raw29664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29664 raw29664Labels permutation434 hz
    mixedMoment B raw29664step0 raw29664step0Labels = mixedMoment B raw29664step1 raw29664step1Labels := by
      have ha : raw29664step1 = (fun i j => raw29664step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29664step1 raw29664step0; decide +kernel
      have hl : raw29664step1Labels = raw29664step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29664step0 raw29664step0Labels permutation32 permutation3
    _ = mixedMoment B node2342 node2342Labels := by rfl

def raw29665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29665 raw29665Labels = mixedMoment B node2432 node2432Labels := by
  calc
    mixedMoment B raw29665 raw29665Labels = mixedMoment B raw29665step0 raw29665step0Labels := by
      have ha : raw29665step0 = (fun i j => raw29665 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29665step0 raw29665; decide +kernel
      have hl : raw29665step0Labels = raw29665Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29665 raw29665Labels permutation200 permutation3
    _ = mixedMoment B node2432 node2432Labels := by rfl

def raw29666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29666 raw29666Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw29666 raw29666Labels = mixedMoment B raw29666step0 raw29666step0Labels := by
      have hz : ∀ j, raw29666 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29666step0 = (fun i j => raw29666 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29666step0 raw29666; decide +kernel
      have hl : raw29666step0Labels = raw29666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29666 raw29666Labels permutation434 hz
    mixedMoment B raw29666step0 raw29666step0Labels = mixedMoment B raw29666step1 raw29666step1Labels := by
      have ha : raw29666step1 = (fun i j => raw29666step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29666step1 raw29666step0; decide +kernel
      have hl : raw29666step1Labels = raw29666step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29666step0 raw29666step0Labels permutation36 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw29667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29667 raw29667Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw29667 raw29667Labels = mixedMoment B raw29667step0 raw29667step0Labels := by
      have hz : ∀ j, raw29667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29667step0 = (fun i j => raw29667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29667step0 raw29667; decide +kernel
      have hl : raw29667step0Labels = raw29667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29667 raw29667Labels permutation346 hz
    mixedMoment B raw29667step0 raw29667step0Labels = mixedMoment B raw29667step1 raw29667step1Labels := by
      have ha : raw29667step1 = (fun i j => raw29667step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29667step1 raw29667step0; decide +kernel
      have hl : raw29667step1Labels = raw29667step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29667step0 raw29667step0Labels permutation32 permutation3
    _ = mixedMoment B node2342 node2342Labels := by rfl

def raw29668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29668step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29668 raw29668Labels = mixedMoment B node2432 node2432Labels := by
  calc
    mixedMoment B raw29668 raw29668Labels = mixedMoment B raw29668step0 raw29668step0Labels := by
      have ha : raw29668step0 = (fun i j => raw29668 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29668step0 raw29668; decide +kernel
      have hl : raw29668step0Labels = raw29668Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29668 raw29668Labels permutation176 permutation3
    _ = mixedMoment B node2432 node2432Labels := by rfl

def raw29669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw29669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29669 raw29669Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw29669 raw29669Labels = mixedMoment B raw29669step0 raw29669step0Labels := by
      have hz : ∀ j, raw29669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29669step0 = (fun i j => raw29669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29669step0 raw29669; decide +kernel
      have hl : raw29669step0Labels = raw29669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29669 raw29669Labels permutation346 hz
    mixedMoment B raw29669step0 raw29669step0Labels = mixedMoment B raw29669step1 raw29669step1Labels := by
      have ha : raw29669step1 = (fun i j => raw29669step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29669step1 raw29669step0; decide +kernel
      have hl : raw29669step1Labels = raw29669step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29669step0 raw29669step0Labels permutation36 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw29670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29670step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw29670step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29670step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw29670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29670 raw29670Labels = mixedMoment B node2344 node2344Labels := by
  calc
    mixedMoment B raw29670 raw29670Labels = mixedMoment B raw29670step0 raw29670step0Labels := by
      have hz : ∀ j, raw29670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29670step0 = (fun i j => raw29670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29670step0 raw29670; decide +kernel
      have hl : raw29670step0Labels = raw29670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29670 raw29670Labels permutation434 hz
    mixedMoment B raw29670step0 raw29670step0Labels = mixedMoment B raw29670step1 raw29670step1Labels := by
      have hz : ∀ j, raw29670step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29670step1 = (fun i j => raw29670step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29670step1 raw29670step0; decide +kernel
      have hl : raw29670step1Labels = raw29670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29670step0 raw29670step0Labels permutation80 hz
    mixedMoment B raw29670step1 raw29670step1Labels = mixedMoment B raw29670step2 raw29670step2Labels := by
      have ha : raw29670step2 = (fun i j => raw29670step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29670step2 raw29670step1; decide +kernel
      have hl : raw29670step2Labels = raw29670step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29670step1 raw29670step1Labels permutation9 permutation3
    _ = mixedMoment B node2344 node2344Labels := by rfl

def raw29671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29671step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29671 raw29671Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw29671 raw29671Labels = mixedMoment B raw29671step0 raw29671step0Labels := by
      have hz : ∀ j, raw29671 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29671step0 = (fun i j => raw29671 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29671step0 raw29671; decide +kernel
      have hl : raw29671step0Labels = raw29671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29671 raw29671Labels permutation434 hz
    mixedMoment B raw29671step0 raw29671step0Labels = mixedMoment B raw29671step1 raw29671step1Labels := by
      have ha : raw29671step1 = (fun i j => raw29671step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29671step1 raw29671step0; decide +kernel
      have hl : raw29671step1Labels = raw29671step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29671step0 raw29671step0Labels permutation125 permutation3
    mixedMoment B raw29671step1 raw29671step1Labels = mixedMoment B raw29671step2 raw29671step2Labels := by
      have ha : raw29671step2 = -raw29671step1 := by apply Matrix.ext; change ∀ i j, raw29671step2 i j = -(raw29671step1 i j); unfold raw29671step2 raw29671step1; decide +kernel
      have hl : raw29671step2Labels = raw29671step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2334 node2334Labels := by rfl

def raw29672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw29672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29672step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29672step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29672 raw29672Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw29672 raw29672Labels = mixedMoment B raw29672step0 raw29672step0Labels := by
      have hz : ∀ j, raw29672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29672step0 = (fun i j => raw29672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29672step0 raw29672; decide +kernel
      have hl : raw29672step0Labels = raw29672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29672 raw29672Labels permutation346 hz
    mixedMoment B raw29672step0 raw29672step0Labels = mixedMoment B raw29672step1 raw29672step1Labels := by
      have ha : raw29672step1 = (fun i j => raw29672step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29672step1 raw29672step0; decide +kernel
      have hl : raw29672step1Labels = raw29672step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29672step0 raw29672step0Labels permutation125 permutation3
    mixedMoment B raw29672step1 raw29672step1Labels = mixedMoment B raw29672step2 raw29672step2Labels := by
      have ha : raw29672step2 = -raw29672step1 := by apply Matrix.ext; change ∀ i j, raw29672step2 i j = -(raw29672step1 i j); unfold raw29672step2 raw29672step1; decide +kernel
      have hl : raw29672step2Labels = raw29672step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2334 node2334Labels := by rfl

def raw29673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw29673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![3, -2, -1], ![1, 0, -1]]
def raw29673step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29673 raw29673Labels = mixedMoment B node2598 node2598Labels := by
  calc
    mixedMoment B raw29673 raw29673Labels = mixedMoment B raw29673step0 raw29673step0Labels := by
      have hz : ∀ j, raw29673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29673step0 = (fun i j => raw29673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29673step0 raw29673; decide +kernel
      have hl : raw29673step0Labels = raw29673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29673 raw29673Labels permutation434 hz
    mixedMoment B raw29673step0 raw29673step0Labels = mixedMoment B raw29673step1 raw29673step1Labels := by
      have hz : ∀ j, raw29673step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29673step1 = (fun i j => raw29673step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29673step1 raw29673step0; decide +kernel
      have hl : raw29673step1Labels = raw29673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29673step0 raw29673step0Labels permutation80 hz
    mixedMoment B raw29673step1 raw29673step1Labels = mixedMoment B raw29673step2 raw29673step2Labels := by
      have ha : raw29673step2 = (fun i j => raw29673step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29673step2 raw29673step1; decide +kernel
      have hl : raw29673step2Labels = raw29673step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29673step1 raw29673step1Labels permutation9 permutation3
    _ = mixedMoment B node2598 node2598Labels := by rfl

def raw29674 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29674step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29674step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw29674step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29674 raw29674Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw29674 raw29674Labels = mixedMoment B raw29674step0 raw29674step0Labels := by
      have hz : ∀ j, raw29674 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29674step0 = (fun i j => raw29674 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29674step0 raw29674; decide +kernel
      have hl : raw29674step0Labels = raw29674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29674 raw29674Labels permutation434 hz
    mixedMoment B raw29674step0 raw29674step0Labels = mixedMoment B raw29674step1 raw29674step1Labels := by
      have hz : ∀ j, raw29674step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29674step1 = (fun i j => raw29674step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29674step1 raw29674step0; decide +kernel
      have hl : raw29674step1Labels = raw29674step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29674step0 raw29674step0Labels permutation80 hz
    mixedMoment B raw29674step1 raw29674step1Labels = mixedMoment B raw29674step2 raw29674step2Labels := by
      have ha : raw29674step2 = (fun i j => raw29674step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29674step2 raw29674step1; decide +kernel
      have hl : raw29674step2Labels = raw29674step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29674step1 raw29674step1Labels permutation8 permutation7
    mixedMoment B raw29674step2 raw29674step2Labels = mixedMoment B raw29674step3 raw29674step3Labels := by
      have ha : raw29674step3 = raw29674step2 := by apply Matrix.ext; unfold raw29674step3 raw29674step2; decide +kernel
      have hl : raw29674step2Labels = labelEmbedding10 ∘ raw29674step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29674step2 raw29674step2Labels raw29674step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw29675 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29675step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29675 raw29675Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw29675 raw29675Labels = mixedMoment B raw29675step0 raw29675step0Labels := by
      have hz : ∀ j, raw29675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29675step0 = (fun i j => raw29675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29675step0 raw29675; decide +kernel
      have hl : raw29675step0Labels = raw29675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29675 raw29675Labels permutation434 hz
    mixedMoment B raw29675step0 raw29675step0Labels = mixedMoment B raw29675step1 raw29675step1Labels := by
      have ha : raw29675step1 = (fun i j => raw29675step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29675step1 raw29675step0; decide +kernel
      have hl : raw29675step1Labels = raw29675step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29675step0 raw29675step0Labels permutation32 permutation7
    mixedMoment B raw29675step1 raw29675step1Labels = mixedMoment B raw29675step2 raw29675step2Labels := by
      have ha : raw29675step2 = raw29675step1 := by apply Matrix.ext; unfold raw29675step2 raw29675step1; decide +kernel
      have hl : raw29675step1Labels = labelEmbedding10 ∘ raw29675step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29675step1 raw29675step1Labels raw29675step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw29676 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29676step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29676 raw29676Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw29676 raw29676Labels = mixedMoment B raw29676step0 raw29676step0Labels := by
      have hz : ∀ j, raw29676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29676step0 = (fun i j => raw29676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29676step0 raw29676; decide +kernel
      have hl : raw29676step0Labels = raw29676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29676 raw29676Labels permutation346 hz
    mixedMoment B raw29676step0 raw29676step0Labels = mixedMoment B raw29676step1 raw29676step1Labels := by
      have ha : raw29676step1 = (fun i j => raw29676step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29676step1 raw29676step0; decide +kernel
      have hl : raw29676step1Labels = raw29676step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29676step0 raw29676step0Labels permutation32 permutation7
    mixedMoment B raw29676step1 raw29676step1Labels = mixedMoment B raw29676step2 raw29676step2Labels := by
      have ha : raw29676step2 = raw29676step1 := by apply Matrix.ext; unfold raw29676step2 raw29676step1; decide +kernel
      have hl : raw29676step1Labels = labelEmbedding10 ∘ raw29676step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29676step1 raw29676step1Labels raw29676step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw29677 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29677step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29677step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29677 raw29677Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw29677 raw29677Labels = mixedMoment B raw29677step0 raw29677step0Labels := by
      have hz : ∀ j, raw29677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29677step0 = (fun i j => raw29677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29677step0 raw29677; decide +kernel
      have hl : raw29677step0Labels = raw29677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29677 raw29677Labels permutation434 hz
    mixedMoment B raw29677step0 raw29677step0Labels = mixedMoment B raw29677step1 raw29677step1Labels := by
      have hz : ∀ j, raw29677step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29677step1 = (fun i j => raw29677step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29677step1 raw29677step0; decide +kernel
      have hl : raw29677step1Labels = raw29677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29677step0 raw29677step0Labels permutation80 hz
    mixedMoment B raw29677step1 raw29677step1Labels = mixedMoment B raw29677step2 raw29677step2Labels := by
      have ha : raw29677step2 = (fun i j => raw29677step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29677step2 raw29677step1; decide +kernel
      have hl : raw29677step2Labels = raw29677step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29677step1 raw29677step1Labels permutation8 permutation7
    mixedMoment B raw29677step2 raw29677step2Labels = mixedMoment B raw29677step3 raw29677step3Labels := by
      have ha : raw29677step3 = raw29677step2 := by apply Matrix.ext; unfold raw29677step3 raw29677step2; decide +kernel
      have hl : raw29677step2Labels = labelEmbedding10 ∘ raw29677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29677step2 raw29677step2Labels raw29677step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5111 node5111Labels := by rfl

def raw29678 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29678step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29678step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29678step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29678 raw29678Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw29678 raw29678Labels = mixedMoment B raw29678step0 raw29678step0Labels := by
      have hz : ∀ j, raw29678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29678step0 = (fun i j => raw29678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29678step0 raw29678; decide +kernel
      have hl : raw29678step0Labels = raw29678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29678 raw29678Labels permutation434 hz
    mixedMoment B raw29678step0 raw29678step0Labels = mixedMoment B raw29678step1 raw29678step1Labels := by
      have hz : ∀ j, raw29678step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29678step1 = (fun i j => raw29678step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29678step1 raw29678step0; decide +kernel
      have hl : raw29678step1Labels = raw29678step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29678step0 raw29678step0Labels permutation80 hz
    mixedMoment B raw29678step1 raw29678step1Labels = mixedMoment B raw29678step2 raw29678step2Labels := by
      have ha : raw29678step2 = (fun i j => raw29678step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29678step2 raw29678step1; decide +kernel
      have hl : raw29678step2Labels = raw29678step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29678step1 raw29678step1Labels permutation8 permutation6
    mixedMoment B raw29678step2 raw29678step2Labels = mixedMoment B raw29678step3 raw29678step3Labels := by
      have ha : raw29678step3 = raw29678step2 := by apply Matrix.ext; unfold raw29678step3 raw29678step2; decide +kernel
      have hl : raw29678step2Labels = labelEmbedding9 ∘ raw29678step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29678step2 raw29678step2Labels raw29678step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4875 node4875Labels := by rfl

def raw29679 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29679step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29679 raw29679Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw29679 raw29679Labels = mixedMoment B raw29679step0 raw29679step0Labels := by
      have hz : ∀ j, raw29679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29679step0 = (fun i j => raw29679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29679step0 raw29679; decide +kernel
      have hl : raw29679step0Labels = raw29679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29679 raw29679Labels permutation434 hz
    mixedMoment B raw29679step0 raw29679step0Labels = mixedMoment B raw29679step1 raw29679step1Labels := by
      have ha : raw29679step1 = (fun i j => raw29679step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29679step1 raw29679step0; decide +kernel
      have hl : raw29679step1Labels = raw29679step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29679step0 raw29679step0Labels permutation32 permutation6
    mixedMoment B raw29679step1 raw29679step1Labels = mixedMoment B raw29679step2 raw29679step2Labels := by
      have ha : raw29679step2 = raw29679step1 := by apply Matrix.ext; unfold raw29679step2 raw29679step1; decide +kernel
      have hl : raw29679step1Labels = labelEmbedding9 ∘ raw29679step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29679step1 raw29679step1Labels raw29679step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw29680 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29680step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw29680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29680 raw29680Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw29680 raw29680Labels = mixedMoment B raw29680step0 raw29680step0Labels := by
      have hz : ∀ j, raw29680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29680step0 = (fun i j => raw29680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29680step0 raw29680; decide +kernel
      have hl : raw29680step0Labels = raw29680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29680 raw29680Labels permutation346 hz
    mixedMoment B raw29680step0 raw29680step0Labels = mixedMoment B raw29680step1 raw29680step1Labels := by
      have ha : raw29680step1 = (fun i j => raw29680step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29680step1 raw29680step0; decide +kernel
      have hl : raw29680step1Labels = raw29680step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29680step0 raw29680step0Labels permutation32 permutation6
    mixedMoment B raw29680step1 raw29680step1Labels = mixedMoment B raw29680step2 raw29680step2Labels := by
      have ha : raw29680step2 = raw29680step1 := by apply Matrix.ext; unfold raw29680step2 raw29680step1; decide +kernel
      have hl : raw29680step1Labels = labelEmbedding9 ∘ raw29680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29680step1 raw29680step1Labels raw29680step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw29681 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29681step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29681step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29681step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29681 raw29681Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw29681 raw29681Labels = mixedMoment B raw29681step0 raw29681step0Labels := by
      have hz : ∀ j, raw29681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29681step0 = (fun i j => raw29681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29681step0 raw29681; decide +kernel
      have hl : raw29681step0Labels = raw29681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29681 raw29681Labels permutation434 hz
    mixedMoment B raw29681step0 raw29681step0Labels = mixedMoment B raw29681step1 raw29681step1Labels := by
      have hz : ∀ j, raw29681step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29681step1 = (fun i j => raw29681step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29681step1 raw29681step0; decide +kernel
      have hl : raw29681step1Labels = raw29681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29681step0 raw29681step0Labels permutation80 hz
    mixedMoment B raw29681step1 raw29681step1Labels = mixedMoment B raw29681step2 raw29681step2Labels := by
      have ha : raw29681step2 = (fun i j => raw29681step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29681step2 raw29681step1; decide +kernel
      have hl : raw29681step2Labels = raw29681step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29681step1 raw29681step1Labels permutation9 permutation6
    mixedMoment B raw29681step2 raw29681step2Labels = mixedMoment B raw29681step3 raw29681step3Labels := by
      have ha : raw29681step3 = raw29681step2 := by apply Matrix.ext; unfold raw29681step3 raw29681step2; decide +kernel
      have hl : raw29681step2Labels = labelEmbedding9 ∘ raw29681step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29681step2 raw29681step2Labels raw29681step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw29682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29682step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29682 raw29682Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw29682 raw29682Labels = mixedMoment B raw29682step0 raw29682step0Labels := by
      have hz : ∀ j, raw29682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29682step0 = (fun i j => raw29682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29682step0 raw29682; decide +kernel
      have hl : raw29682step0Labels = raw29682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29682 raw29682Labels permutation434 hz
    mixedMoment B raw29682step0 raw29682step0Labels = mixedMoment B raw29682step1 raw29682step1Labels := by
      have ha : raw29682step1 = (fun i j => raw29682step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29682step1 raw29682step0; decide +kernel
      have hl : raw29682step1Labels = raw29682step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29682step0 raw29682step0Labels permutation32 permutation6
    mixedMoment B raw29682step1 raw29682step1Labels = mixedMoment B raw29682step2 raw29682step2Labels := by
      have ha : raw29682step2 = raw29682step1 := by apply Matrix.ext; unfold raw29682step2 raw29682step1; decide +kernel
      have hl : raw29682step1Labels = labelEmbedding9 ∘ raw29682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29682step1 raw29682step1Labels raw29682step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw29683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29683step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29683 raw29683Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw29683 raw29683Labels = mixedMoment B raw29683step0 raw29683step0Labels := by
      have hz : ∀ j, raw29683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29683step0 = (fun i j => raw29683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29683step0 raw29683; decide +kernel
      have hl : raw29683step0Labels = raw29683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29683 raw29683Labels permutation434 hz
    mixedMoment B raw29683step0 raw29683step0Labels = mixedMoment B raw29683step1 raw29683step1Labels := by
      have ha : raw29683step1 = (fun i j => raw29683step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29683step1 raw29683step0; decide +kernel
      have hl : raw29683step1Labels = raw29683step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29683step0 raw29683step0Labels permutation32 permutation6
    mixedMoment B raw29683step1 raw29683step1Labels = mixedMoment B raw29683step2 raw29683step2Labels := by
      have ha : raw29683step2 = raw29683step1 := by apply Matrix.ext; unfold raw29683step2 raw29683step1; decide +kernel
      have hl : raw29683step1Labels = labelEmbedding9 ∘ raw29683step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29683step1 raw29683step1Labels raw29683step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw29684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29684step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29684 raw29684Labels = mixedMoment B node5130 node5130Labels := by
  calc
    mixedMoment B raw29684 raw29684Labels = mixedMoment B raw29684step0 raw29684step0Labels := by
      have ha : raw29684step0 = (fun i j => raw29684 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29684step0 raw29684; decide +kernel
      have hl : raw29684step0Labels = raw29684Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29684 raw29684Labels permutation158 permutation6
    mixedMoment B raw29684step0 raw29684step0Labels = mixedMoment B raw29684step1 raw29684step1Labels := by
      have ha : raw29684step1 = raw29684step0 := by apply Matrix.ext; unfold raw29684step1 raw29684step0; decide +kernel
      have hl : raw29684step0Labels = labelEmbedding9 ∘ raw29684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29684step0 raw29684step0Labels raw29684step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5130 node5130Labels := by rfl

def raw29685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29685step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29685 raw29685Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw29685 raw29685Labels = mixedMoment B raw29685step0 raw29685step0Labels := by
      have hz : ∀ j, raw29685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29685step0 = (fun i j => raw29685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29685step0 raw29685; decide +kernel
      have hl : raw29685step0Labels = raw29685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29685 raw29685Labels permutation434 hz
    mixedMoment B raw29685step0 raw29685step0Labels = mixedMoment B raw29685step1 raw29685step1Labels := by
      have ha : raw29685step1 = (fun i j => raw29685step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29685step1 raw29685step0; decide +kernel
      have hl : raw29685step1Labels = raw29685step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29685step0 raw29685step0Labels permutation33 permutation6
    mixedMoment B raw29685step1 raw29685step1Labels = mixedMoment B raw29685step2 raw29685step2Labels := by
      have ha : raw29685step2 = raw29685step1 := by apply Matrix.ext; unfold raw29685step2 raw29685step1; decide +kernel
      have hl : raw29685step1Labels = labelEmbedding9 ∘ raw29685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29685step1 raw29685step1Labels raw29685step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw29686 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29686step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29686 raw29686Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw29686 raw29686Labels = mixedMoment B raw29686step0 raw29686step0Labels := by
      have hz : ∀ j, raw29686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29686step0 = (fun i j => raw29686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29686step0 raw29686; decide +kernel
      have hl : raw29686step0Labels = raw29686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29686 raw29686Labels permutation346 hz
    mixedMoment B raw29686step0 raw29686step0Labels = mixedMoment B raw29686step1 raw29686step1Labels := by
      have ha : raw29686step1 = (fun i j => raw29686step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29686step1 raw29686step0; decide +kernel
      have hl : raw29686step1Labels = raw29686step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29686step0 raw29686step0Labels permutation32 permutation6
    mixedMoment B raw29686step1 raw29686step1Labels = mixedMoment B raw29686step2 raw29686step2Labels := by
      have ha : raw29686step2 = raw29686step1 := by apply Matrix.ext; unfold raw29686step2 raw29686step1; decide +kernel
      have hl : raw29686step1Labels = labelEmbedding9 ∘ raw29686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29686step1 raw29686step1Labels raw29686step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw29687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29687step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29687 raw29687Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw29687 raw29687Labels = mixedMoment B raw29687step0 raw29687step0Labels := by
      have hz : ∀ j, raw29687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29687step0 = (fun i j => raw29687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29687step0 raw29687; decide +kernel
      have hl : raw29687step0Labels = raw29687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29687 raw29687Labels permutation346 hz
    mixedMoment B raw29687step0 raw29687step0Labels = mixedMoment B raw29687step1 raw29687step1Labels := by
      have ha : raw29687step1 = (fun i j => raw29687step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29687step1 raw29687step0; decide +kernel
      have hl : raw29687step1Labels = raw29687step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29687step0 raw29687step0Labels permutation32 permutation6
    mixedMoment B raw29687step1 raw29687step1Labels = mixedMoment B raw29687step2 raw29687step2Labels := by
      have ha : raw29687step2 = raw29687step1 := by apply Matrix.ext; unfold raw29687step2 raw29687step1; decide +kernel
      have hl : raw29687step1Labels = labelEmbedding9 ∘ raw29687step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29687step1 raw29687step1Labels raw29687step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw29688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29688step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29688 raw29688Labels = mixedMoment B node5130 node5130Labels := by
  calc
    mixedMoment B raw29688 raw29688Labels = mixedMoment B raw29688step0 raw29688step0Labels := by
      have ha : raw29688step0 = (fun i j => raw29688 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29688step0 raw29688; decide +kernel
      have hl : raw29688step0Labels = raw29688Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29688 raw29688Labels permutation152 permutation6
    mixedMoment B raw29688step0 raw29688step0Labels = mixedMoment B raw29688step1 raw29688step1Labels := by
      have ha : raw29688step1 = raw29688step0 := by apply Matrix.ext; unfold raw29688step1 raw29688step0; decide +kernel
      have hl : raw29688step0Labels = labelEmbedding9 ∘ raw29688step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29688step0 raw29688step0Labels raw29688step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5130 node5130Labels := by rfl

def raw29689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29689step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29689 raw29689Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw29689 raw29689Labels = mixedMoment B raw29689step0 raw29689step0Labels := by
      have hz : ∀ j, raw29689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29689step0 = (fun i j => raw29689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29689step0 raw29689; decide +kernel
      have hl : raw29689step0Labels = raw29689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29689 raw29689Labels permutation346 hz
    mixedMoment B raw29689step0 raw29689step0Labels = mixedMoment B raw29689step1 raw29689step1Labels := by
      have ha : raw29689step1 = (fun i j => raw29689step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29689step1 raw29689step0; decide +kernel
      have hl : raw29689step1Labels = raw29689step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29689step0 raw29689step0Labels permutation33 permutation6
    mixedMoment B raw29689step1 raw29689step1Labels = mixedMoment B raw29689step2 raw29689step2Labels := by
      have ha : raw29689step2 = raw29689step1 := by apply Matrix.ext; unfold raw29689step2 raw29689step1; decide +kernel
      have hl : raw29689step1Labels = labelEmbedding9 ∘ raw29689step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29689step1 raw29689step1Labels raw29689step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw29690 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw29690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29690step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29690step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29690 raw29690Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw29690 raw29690Labels = mixedMoment B raw29690step0 raw29690step0Labels := by
      have hz : ∀ j, raw29690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29690step0 = (fun i j => raw29690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29690step0 raw29690; decide +kernel
      have hl : raw29690step0Labels = raw29690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29690 raw29690Labels permutation434 hz
    mixedMoment B raw29690step0 raw29690step0Labels = mixedMoment B raw29690step1 raw29690step1Labels := by
      have hz : ∀ j, raw29690step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29690step1 = (fun i j => raw29690step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29690step1 raw29690step0; decide +kernel
      have hl : raw29690step1Labels = raw29690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29690step0 raw29690step0Labels permutation80 hz
    mixedMoment B raw29690step1 raw29690step1Labels = mixedMoment B raw29690step2 raw29690step2Labels := by
      have ha : raw29690step2 = (fun i j => raw29690step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29690step2 raw29690step1; decide +kernel
      have hl : raw29690step2Labels = raw29690step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29690step1 raw29690step1Labels permutation9 permutation6
    mixedMoment B raw29690step2 raw29690step2Labels = mixedMoment B raw29690step3 raw29690step3Labels := by
      have ha : raw29690step3 = raw29690step2 := by apply Matrix.ext; unfold raw29690step3 raw29690step2; decide +kernel
      have hl : raw29690step2Labels = labelEmbedding9 ∘ raw29690step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29690step2 raw29690step2Labels raw29690step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw29691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw29691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29691step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29691step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29691step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29691 raw29691Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw29691 raw29691Labels = mixedMoment B raw29691step0 raw29691step0Labels := by
      have hz : ∀ j, raw29691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29691step0 = (fun i j => raw29691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29691step0 raw29691; decide +kernel
      have hl : raw29691step0Labels = raw29691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29691 raw29691Labels permutation434 hz
    mixedMoment B raw29691step0 raw29691step0Labels = mixedMoment B raw29691step1 raw29691step1Labels := by
      have hz : ∀ j, raw29691step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29691step1 = (fun i j => raw29691step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29691step1 raw29691step0; decide +kernel
      have hl : raw29691step1Labels = raw29691step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29691step0 raw29691step0Labels permutation80 hz
    mixedMoment B raw29691step1 raw29691step1Labels = mixedMoment B raw29691step2 raw29691step2Labels := by
      have ha : raw29691step2 = (fun i j => raw29691step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29691step2 raw29691step1; decide +kernel
      have hl : raw29691step2Labels = raw29691step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29691step1 raw29691step1Labels permutation9 permutation6
    mixedMoment B raw29691step2 raw29691step2Labels = mixedMoment B raw29691step3 raw29691step3Labels := by
      have ha : raw29691step3 = raw29691step2 := by apply Matrix.ext; unfold raw29691step3 raw29691step2; decide +kernel
      have hl : raw29691step2Labels = labelEmbedding9 ∘ raw29691step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29691step2 raw29691step2Labels raw29691step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5111 node5111Labels := by rfl

def raw29692 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29692step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29692step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29692 raw29692Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw29692 raw29692Labels = mixedMoment B raw29692step0 raw29692step0Labels := by
      have hz : ∀ j, raw29692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29692step0 = (fun i j => raw29692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29692step0 raw29692; decide +kernel
      have hl : raw29692step0Labels = raw29692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29692 raw29692Labels permutation434 hz
    mixedMoment B raw29692step0 raw29692step0Labels = mixedMoment B raw29692step1 raw29692step1Labels := by
      have ha : raw29692step1 = (fun i j => raw29692step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29692step1 raw29692step0; decide +kernel
      have hl : raw29692step1Labels = raw29692step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29692step0 raw29692step0Labels permutation33 permutation6
    mixedMoment B raw29692step1 raw29692step1Labels = mixedMoment B raw29692step2 raw29692step2Labels := by
      have ha : raw29692step2 = raw29692step1 := by apply Matrix.ext; unfold raw29692step2 raw29692step1; decide +kernel
      have hl : raw29692step1Labels = labelEmbedding9 ∘ raw29692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29692step1 raw29692step1Labels raw29692step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw29693 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw29693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29693step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29693 raw29693Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw29693 raw29693Labels = mixedMoment B raw29693step0 raw29693step0Labels := by
      have hz : ∀ j, raw29693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29693step0 = (fun i j => raw29693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29693step0 raw29693; decide +kernel
      have hl : raw29693step0Labels = raw29693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29693 raw29693Labels permutation346 hz
    mixedMoment B raw29693step0 raw29693step0Labels = mixedMoment B raw29693step1 raw29693step1Labels := by
      have ha : raw29693step1 = (fun i j => raw29693step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29693step1 raw29693step0; decide +kernel
      have hl : raw29693step1Labels = raw29693step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29693step0 raw29693step0Labels permutation33 permutation6
    mixedMoment B raw29693step1 raw29693step1Labels = mixedMoment B raw29693step2 raw29693step2Labels := by
      have ha : raw29693step2 = raw29693step1 := by apply Matrix.ext; unfold raw29693step2 raw29693step1; decide +kernel
      have hl : raw29693step1Labels = labelEmbedding9 ∘ raw29693step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29693step1 raw29693step1Labels raw29693step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw29694 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw29694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw29694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw29694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29694step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29694step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29694 raw29694Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw29694 raw29694Labels = mixedMoment B raw29694step0 raw29694step0Labels := by
      have hz : ∀ j, raw29694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29694step0 = (fun i j => raw29694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29694step0 raw29694; decide +kernel
      have hl : raw29694step0Labels = raw29694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29694 raw29694Labels permutation434 hz
    mixedMoment B raw29694step0 raw29694step0Labels = mixedMoment B raw29694step1 raw29694step1Labels := by
      have hz : ∀ j, raw29694step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29694step1 = (fun i j => raw29694step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29694step1 raw29694step0; decide +kernel
      have hl : raw29694step1Labels = raw29694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29694step0 raw29694step0Labels permutation80 hz
    mixedMoment B raw29694step1 raw29694step1Labels = mixedMoment B raw29694step2 raw29694step2Labels := by
      have ha : raw29694step2 = (fun i j => raw29694step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29694step2 raw29694step1; decide +kernel
      have hl : raw29694step2Labels = raw29694step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29694step1 raw29694step1Labels permutation9 permutation6
    mixedMoment B raw29694step2 raw29694step2Labels = mixedMoment B raw29694step3 raw29694step3Labels := by
      have ha : raw29694step3 = raw29694step2 := by apply Matrix.ext; unfold raw29694step3 raw29694step2; decide +kernel
      have hl : raw29694step2Labels = labelEmbedding9 ∘ raw29694step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29694step2 raw29694step2Labels raw29694step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw29695 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29695step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw29695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29695 raw29695Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw29695 raw29695Labels = mixedMoment B raw29695step0 raw29695step0Labels := by
      have hz : ∀ j, raw29695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29695step0 = (fun i j => raw29695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29695step0 raw29695; decide +kernel
      have hl : raw29695step0Labels = raw29695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29695 raw29695Labels permutation434 hz
    mixedMoment B raw29695step0 raw29695step0Labels = mixedMoment B raw29695step1 raw29695step1Labels := by
      have hz : ∀ j, raw29695step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29695step1 = (fun i j => raw29695step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29695step1 raw29695step0; decide +kernel
      have hl : raw29695step1Labels = raw29695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29695step0 raw29695step0Labels permutation80 hz
    mixedMoment B raw29695step1 raw29695step1Labels = mixedMoment B raw29695step2 raw29695step2Labels := by
      have ha : raw29695step2 = (fun i j => raw29695step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29695step2 raw29695step1; decide +kernel
      have hl : raw29695step2Labels = raw29695step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29695step1 raw29695step1Labels permutation8 permutation6
    mixedMoment B raw29695step2 raw29695step2Labels = mixedMoment B raw29695step3 raw29695step3Labels := by
      have ha : raw29695step3 = raw29695step2 := by apply Matrix.ext; unfold raw29695step3 raw29695step2; decide +kernel
      have hl : raw29695step2Labels = labelEmbedding9 ∘ raw29695step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29695step2 raw29695step2Labels raw29695step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
