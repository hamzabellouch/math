import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw36224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw36224step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36224step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36224 raw36224Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw36224 raw36224Labels = mixedMoment B raw36224step0 raw36224step0Labels := by
      have hz : ∀ j, raw36224 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36224step0 = (fun i j => raw36224 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36224step0 raw36224; decide +kernel
      have hl : raw36224step0Labels = raw36224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36224 raw36224Labels permutation346 hz
    mixedMoment B raw36224step0 raw36224step0Labels = mixedMoment B raw36224step1 raw36224step1Labels := by
      have ha : raw36224step1 = (fun i j => raw36224step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36224step1 raw36224step0; decide +kernel
      have hl : raw36224step1Labels = raw36224step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36224step0 raw36224step0Labels permutation144 permutation7
    mixedMoment B raw36224step1 raw36224step1Labels = mixedMoment B raw36224step2 raw36224step2Labels := by
      have ha : raw36224step2 = raw36224step1 := by apply Matrix.ext; unfold raw36224step2 raw36224step1; decide +kernel
      have hl : raw36224step1Labels = labelEmbedding1 ∘ raw36224step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36224step1 raw36224step1Labels raw36224step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

def raw36225 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw36225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw36225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36225step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36225step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36225step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36225 raw36225Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw36225 raw36225Labels = mixedMoment B raw36225step0 raw36225step0Labels := by
      have hz : ∀ j, raw36225 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36225step0 = (fun i j => raw36225 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36225step0 raw36225; decide +kernel
      have hl : raw36225step0Labels = raw36225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36225 raw36225Labels permutation346 hz
    mixedMoment B raw36225step0 raw36225step0Labels = mixedMoment B raw36225step1 raw36225step1Labels := by
      have ha : raw36225step1 = (fun i j => raw36225step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36225step1 raw36225step0; decide +kernel
      have hl : raw36225step1Labels = raw36225step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36225step0 raw36225step0Labels permutation34 permutation7
    mixedMoment B raw36225step1 raw36225step1Labels = mixedMoment B raw36225step2 raw36225step2Labels := by
      have ha : raw36225step2 = raw36225step1 := by apply Matrix.ext; unfold raw36225step2 raw36225step1; decide +kernel
      have hl : raw36225step1Labels = labelEmbedding10 ∘ raw36225step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36225step1 raw36225step1Labels raw36225step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw36226 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw36226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36226step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36226 raw36226Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw36226 raw36226Labels = mixedMoment B raw36226step0 raw36226step0Labels := by
      have ha : raw36226step0 = (fun i j => raw36226 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36226step0 raw36226; decide +kernel
      have hl : raw36226step0Labels = raw36226Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36226 raw36226Labels permutation154 permutation7
    mixedMoment B raw36226step0 raw36226step0Labels = mixedMoment B raw36226step1 raw36226step1Labels := by
      have ha : raw36226step1 = raw36226step0 := by apply Matrix.ext; unfold raw36226step1 raw36226step0; decide +kernel
      have hl : raw36226step0Labels = labelEmbedding10 ∘ raw36226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36226step0 raw36226step0Labels raw36226step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw36227 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw36227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw36227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36227 raw36227Labels = mixedMoment B node5364 node5364Labels := by
  calc
    mixedMoment B raw36227 raw36227Labels = mixedMoment B raw36227step0 raw36227step0Labels := by
      have hz : ∀ j, raw36227 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36227step0 = (fun i j => raw36227 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36227step0 raw36227; decide +kernel
      have hl : raw36227step0Labels = raw36227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36227 raw36227Labels permutation346 hz
    mixedMoment B raw36227step0 raw36227step0Labels = mixedMoment B raw36227step1 raw36227step1Labels := by
      have ha : raw36227step1 = (fun i j => raw36227step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36227step1 raw36227step0; decide +kernel
      have hl : raw36227step1Labels = raw36227step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36227step0 raw36227step0Labels permutation145 permutation2
    _ = mixedMoment B node5364 node5364Labels := by rfl

def raw36228 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw36228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw36228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36228step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36228step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36228 raw36228Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw36228 raw36228Labels = mixedMoment B raw36228step0 raw36228step0Labels := by
      have hz : ∀ j, raw36228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36228step0 = (fun i j => raw36228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36228step0 raw36228; decide +kernel
      have hl : raw36228step0Labels = raw36228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36228 raw36228Labels permutation346 hz
    mixedMoment B raw36228step0 raw36228step0Labels = mixedMoment B raw36228step1 raw36228step1Labels := by
      have ha : raw36228step1 = (fun i j => raw36228step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36228step1 raw36228step0; decide +kernel
      have hl : raw36228step1Labels = raw36228step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36228step0 raw36228step0Labels permutation34 permutation7
    mixedMoment B raw36228step1 raw36228step1Labels = mixedMoment B raw36228step2 raw36228step2Labels := by
      have ha : raw36228step2 = raw36228step1 := by apply Matrix.ext; unfold raw36228step2 raw36228step1; decide +kernel
      have hl : raw36228step1Labels = labelEmbedding10 ∘ raw36228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36228step1 raw36228step1Labels raw36228step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw36229 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw36229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw36229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36229 raw36229Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw36229 raw36229Labels = mixedMoment B raw36229step0 raw36229step0Labels := by
      have hz : ∀ j, raw36229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36229step0 = (fun i j => raw36229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36229step0 raw36229; decide +kernel
      have hl : raw36229step0Labels = raw36229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36229 raw36229Labels permutation346 hz
    mixedMoment B raw36229step0 raw36229step0Labels = mixedMoment B raw36229step1 raw36229step1Labels := by
      have ha : raw36229step1 = (fun i j => raw36229step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36229step1 raw36229step0; decide +kernel
      have hl : raw36229step1Labels = raw36229step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36229step0 raw36229step0Labels permutation145 permutation2
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw36230 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw36230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36230step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36230 raw36230Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw36230 raw36230Labels = mixedMoment B raw36230step0 raw36230step0Labels := by
      have ha : raw36230step0 = (fun i j => raw36230 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36230step0 raw36230; decide +kernel
      have hl : raw36230step0Labels = raw36230Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36230 raw36230Labels permutation265 permutation6
    mixedMoment B raw36230step0 raw36230step0Labels = mixedMoment B raw36230step1 raw36230step1Labels := by
      have ha : raw36230step1 = raw36230step0 := by apply Matrix.ext; unfold raw36230step1 raw36230step0; decide +kernel
      have hl : raw36230step0Labels = labelEmbedding9 ∘ raw36230step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36230step0 raw36230step0Labels raw36230step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw36231 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw36231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36231 raw36231Labels = mixedMoment B node5362 node5362Labels := by
  calc
    mixedMoment B raw36231 raw36231Labels = mixedMoment B raw36231step0 raw36231step0Labels := by
      have ha : raw36231step0 = (fun i j => raw36231 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36231step0 raw36231; decide +kernel
      have hl : raw36231step0Labels = raw36231Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36231 raw36231Labels permutation663 permutation2
    _ = mixedMoment B node5362 node5362Labels := by rfl

def raw36232 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw36232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36232 raw36232Labels = mixedMoment B node5092 node5092Labels := by
  calc
    mixedMoment B raw36232 raw36232Labels = mixedMoment B raw36232step0 raw36232step0Labels := by
      have ha : raw36232step0 = (fun i j => raw36232 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36232step0 raw36232; decide +kernel
      have hl : raw36232step0Labels = raw36232Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36232 raw36232Labels permutation663 permutation2
    _ = mixedMoment B node5092 node5092Labels := by rfl

def raw36233 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw36233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw36233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36233step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36233step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36233 raw36233Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw36233 raw36233Labels = mixedMoment B raw36233step0 raw36233step0Labels := by
      have hz : ∀ j, raw36233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36233step0 = (fun i j => raw36233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36233step0 raw36233; decide +kernel
      have hl : raw36233step0Labels = raw36233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36233 raw36233Labels permutation346 hz
    mixedMoment B raw36233step0 raw36233step0Labels = mixedMoment B raw36233step1 raw36233step1Labels := by
      have ha : raw36233step1 = (fun i j => raw36233step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36233step1 raw36233step0; decide +kernel
      have hl : raw36233step1Labels = raw36233step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36233step0 raw36233step0Labels permutation56 permutation6
    mixedMoment B raw36233step1 raw36233step1Labels = mixedMoment B raw36233step2 raw36233step2Labels := by
      have ha : raw36233step2 = raw36233step1 := by apply Matrix.ext; unfold raw36233step2 raw36233step1; decide +kernel
      have hl : raw36233step1Labels = labelEmbedding9 ∘ raw36233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36233step1 raw36233step1Labels raw36233step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw36234 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw36234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36234step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36234step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36234step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36234step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36234step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36234 raw36234Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw36234 raw36234Labels = mixedMoment B raw36234step0 raw36234step0Labels := by
      have ha : raw36234step0 = (fun i j => raw36234 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36234step0 raw36234; decide +kernel
      have hl : raw36234step0Labels = raw36234Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36234 raw36234Labels permutation663 permutation7
    mixedMoment B raw36234step0 raw36234step0Labels = mixedMoment B raw36234step1 raw36234step1Labels := by
      have ha : raw36234step1 = -raw36234step0 := by apply Matrix.ext; change ∀ i j, raw36234step1 i j = -(raw36234step0 i j); unfold raw36234step1 raw36234step0; decide +kernel
      have hl : raw36234step1Labels = raw36234step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36234step1 raw36234step1Labels = mixedMoment B raw36234step2 raw36234step2Labels := by
      have ha : raw36234step2 = raw36234step1 := by apply Matrix.ext; unfold raw36234step2 raw36234step1; decide +kernel
      have hl : raw36234step1Labels = labelEmbedding10 ∘ raw36234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36234step1 raw36234step1Labels raw36234step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5419 node5419Labels := by rfl

def raw36235 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw36235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw36235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36235step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36235step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36235 raw36235Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw36235 raw36235Labels = mixedMoment B raw36235step0 raw36235step0Labels := by
      have hz : ∀ j, raw36235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36235step0 = (fun i j => raw36235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36235step0 raw36235; decide +kernel
      have hl : raw36235step0Labels = raw36235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36235 raw36235Labels permutation346 hz
    mixedMoment B raw36235step0 raw36235step0Labels = mixedMoment B raw36235step1 raw36235step1Labels := by
      have ha : raw36235step1 = (fun i j => raw36235step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36235step1 raw36235step0; decide +kernel
      have hl : raw36235step1Labels = raw36235step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36235step0 raw36235step0Labels permutation144 permutation7
    mixedMoment B raw36235step1 raw36235step1Labels = mixedMoment B raw36235step2 raw36235step2Labels := by
      have ha : raw36235step2 = -raw36235step1 := by apply Matrix.ext; change ∀ i j, raw36235step2 i j = -(raw36235step1 i j); unfold raw36235step2 raw36235step1; decide +kernel
      have hl : raw36235step2Labels = raw36235step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36235step2 raw36235step2Labels = mixedMoment B raw36235step3 raw36235step3Labels := by
      have ha : raw36235step3 = raw36235step2 := by apply Matrix.ext; unfold raw36235step3 raw36235step2; decide +kernel
      have hl : raw36235step2Labels = labelEmbedding10 ∘ raw36235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36235step2 raw36235step2Labels raw36235step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw36236 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw36236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw36236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36236 raw36236Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw36236 raw36236Labels = mixedMoment B raw36236step0 raw36236step0Labels := by
      have hz : ∀ j, raw36236 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36236step0 = (fun i j => raw36236 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36236step0 raw36236; decide +kernel
      have hl : raw36236step0Labels = raw36236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36236 raw36236Labels permutation346 hz
    mixedMoment B raw36236step0 raw36236step0Labels = mixedMoment B raw36236step1 raw36236step1Labels := by
      have ha : raw36236step1 = (fun i j => raw36236step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36236step1 raw36236step0; decide +kernel
      have hl : raw36236step1Labels = raw36236step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36236step0 raw36236step0Labels permutation144 permutation2
    _ = mixedMoment B node5269 node5269Labels := by rfl

def raw36237 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw36237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw36237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw36237step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw36237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36237 raw36237Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw36237 raw36237Labels = mixedMoment B raw36237step0 raw36237step0Labels := by
      have hz : ∀ j, raw36237 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36237step0 = (fun i j => raw36237 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36237step0 raw36237; decide +kernel
      have hl : raw36237step0Labels = raw36237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36237 raw36237Labels permutation346 hz
    mixedMoment B raw36237step0 raw36237step0Labels = mixedMoment B raw36237step1 raw36237step1Labels := by
      have ha : raw36237step1 = (fun i j => raw36237step0 (permutation120 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36237step1 raw36237step0; decide +kernel
      have hl : raw36237step1Labels = raw36237step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36237step0 raw36237step0Labels permutation120 permutation5
    mixedMoment B raw36237step1 raw36237step1Labels = mixedMoment B raw36237step2 raw36237step2Labels := by
      have ha : raw36237step2 = raw36237step1 := by apply Matrix.ext; unfold raw36237step2 raw36237step1; decide +kernel
      have hl : raw36237step1Labels = labelEmbedding8 ∘ raw36237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36237step1 raw36237step1Labels raw36237step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw36238 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw36238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw36238step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw36238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36238 raw36238Labels = mixedMoment B node5285 node5285Labels := by
  calc
    mixedMoment B raw36238 raw36238Labels = mixedMoment B raw36238step0 raw36238step0Labels := by
      have ha : raw36238step0 = (fun i j => raw36238 (permutation563 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36238step0 raw36238; decide +kernel
      have hl : raw36238step0Labels = raw36238Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36238 raw36238Labels permutation563 permutation5
    mixedMoment B raw36238step0 raw36238step0Labels = mixedMoment B raw36238step1 raw36238step1Labels := by
      have ha : raw36238step1 = raw36238step0 := by apply Matrix.ext; unfold raw36238step1 raw36238step0; decide +kernel
      have hl : raw36238step0Labels = labelEmbedding8 ∘ raw36238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36238step0 raw36238step0Labels raw36238step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5285 node5285Labels := by rfl

def raw36239 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw36239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw36239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw36239step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36239step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw36239step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36239 raw36239Labels = mixedMoment B node5298 node5298Labels := by
  calc
    mixedMoment B raw36239 raw36239Labels = mixedMoment B raw36239step0 raw36239step0Labels := by
      have hz : ∀ j, raw36239 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36239step0 = (fun i j => raw36239 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36239step0 raw36239; decide +kernel
      have hl : raw36239step0Labels = raw36239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36239 raw36239Labels permutation346 hz
    mixedMoment B raw36239step0 raw36239step0Labels = mixedMoment B raw36239step1 raw36239step1Labels := by
      have ha : raw36239step1 = (fun i j => raw36239step0 (permutation122 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36239step1 raw36239step0; decide +kernel
      have hl : raw36239step1Labels = raw36239step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36239step0 raw36239step0Labels permutation122 permutation5
    mixedMoment B raw36239step1 raw36239step1Labels = mixedMoment B raw36239step2 raw36239step2Labels := by
      have ha : raw36239step2 = raw36239step1 := by apply Matrix.ext; unfold raw36239step2 raw36239step1; decide +kernel
      have hl : raw36239step1Labels = labelEmbedding8 ∘ raw36239step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36239step1 raw36239step1Labels raw36239step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5298 node5298Labels := by rfl

def raw36240 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw36240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw36240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw36240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36240 raw36240Labels = mixedMoment B node5108 node5108Labels := by
  calc
    mixedMoment B raw36240 raw36240Labels = mixedMoment B raw36240step0 raw36240step0Labels := by
      have hz : ∀ j, raw36240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36240step0 = (fun i j => raw36240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36240step0 raw36240; decide +kernel
      have hl : raw36240step0Labels = raw36240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36240 raw36240Labels permutation346 hz
    mixedMoment B raw36240step0 raw36240step0Labels = mixedMoment B raw36240step1 raw36240step1Labels := by
      have ha : raw36240step1 = (fun i j => raw36240step0 (permutation140 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36240step1 raw36240step0; decide +kernel
      have hl : raw36240step1Labels = raw36240step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36240step0 raw36240step0Labels permutation140 permutation2
    _ = mixedMoment B node5108 node5108Labels := by rfl

def raw36241 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw36241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw36241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36241step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36241step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36241 raw36241Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw36241 raw36241Labels = mixedMoment B raw36241step0 raw36241step0Labels := by
      have hz : ∀ j, raw36241 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36241step0 = (fun i j => raw36241 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36241step0 raw36241; decide +kernel
      have hl : raw36241step0Labels = raw36241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36241 raw36241Labels permutation346 hz
    mixedMoment B raw36241step0 raw36241step0Labels = mixedMoment B raw36241step1 raw36241step1Labels := by
      have ha : raw36241step1 = (fun i j => raw36241step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36241step1 raw36241step0; decide +kernel
      have hl : raw36241step1Labels = raw36241step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36241step0 raw36241step0Labels permutation56 permutation6
    mixedMoment B raw36241step1 raw36241step1Labels = mixedMoment B raw36241step2 raw36241step2Labels := by
      have ha : raw36241step2 = raw36241step1 := by apply Matrix.ext; unfold raw36241step2 raw36241step1; decide +kernel
      have hl : raw36241step1Labels = labelEmbedding9 ∘ raw36241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36241step1 raw36241step1Labels raw36241step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw36242 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw36242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36242step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36242 raw36242Labels = mixedMoment B node5459 node5459Labels := by
  calc
    mixedMoment B raw36242 raw36242Labels = mixedMoment B raw36242step0 raw36242step0Labels := by
      have ha : raw36242step0 = (fun i j => raw36242 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36242step0 raw36242; decide +kernel
      have hl : raw36242step0Labels = raw36242Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36242 raw36242Labels permutation152 permutation6
    mixedMoment B raw36242step0 raw36242step0Labels = mixedMoment B raw36242step1 raw36242step1Labels := by
      have ha : raw36242step1 = raw36242step0 := by apply Matrix.ext; unfold raw36242step1 raw36242step0; decide +kernel
      have hl : raw36242step0Labels = labelEmbedding9 ∘ raw36242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36242step0 raw36242step0Labels raw36242step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5459 node5459Labels := by rfl

def raw36243 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw36243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw36243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36243step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36243 raw36243Labels = mixedMoment B node5463 node5463Labels := by
  calc
    mixedMoment B raw36243 raw36243Labels = mixedMoment B raw36243step0 raw36243step0Labels := by
      have hz : ∀ j, raw36243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36243step0 = (fun i j => raw36243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36243step0 raw36243; decide +kernel
      have hl : raw36243step0Labels = raw36243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36243 raw36243Labels permutation346 hz
    mixedMoment B raw36243step0 raw36243step0Labels = mixedMoment B raw36243step1 raw36243step1Labels := by
      have ha : raw36243step1 = (fun i j => raw36243step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36243step1 raw36243step0; decide +kernel
      have hl : raw36243step1Labels = raw36243step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36243step0 raw36243step0Labels permutation32 permutation6
    mixedMoment B raw36243step1 raw36243step1Labels = mixedMoment B raw36243step2 raw36243step2Labels := by
      have ha : raw36243step2 = raw36243step1 := by apply Matrix.ext; unfold raw36243step2 raw36243step1; decide +kernel
      have hl : raw36243step1Labels = labelEmbedding9 ∘ raw36243step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36243step1 raw36243step1Labels raw36243step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5463 node5463Labels := by rfl

def raw36244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36244step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36244 raw36244Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw36244 raw36244Labels = mixedMoment B raw36244step0 raw36244step0Labels := by
      have ha : raw36244step0 = (fun i j => raw36244 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36244step0 raw36244; decide +kernel
      have hl : raw36244step0Labels = raw36244Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36244 raw36244Labels permutation265 permutation3
    mixedMoment B raw36244step0 raw36244step0Labels = mixedMoment B raw36244step1 raw36244step1Labels := by
      have ha : raw36244step1 = raw36244step0 := by apply Matrix.ext; unfold raw36244step1 raw36244step0; decide +kernel
      have hl : raw36244step0Labels = labelEmbedding6 ∘ raw36244step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36244step0 raw36244step0Labels raw36244step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw36245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36245step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36245 raw36245Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw36245 raw36245Labels = mixedMoment B raw36245step0 raw36245step0Labels := by
      have ha : raw36245step0 = (fun i j => raw36245 (permutation289 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36245step0 raw36245; decide +kernel
      have hl : raw36245step0Labels = raw36245Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36245 raw36245Labels permutation289 permutation3
    mixedMoment B raw36245step0 raw36245step0Labels = mixedMoment B raw36245step1 raw36245step1Labels := by
      have ha : raw36245step1 = raw36245step0 := by apply Matrix.ext; unfold raw36245step1 raw36245step0; decide +kernel
      have hl : raw36245step0Labels = labelEmbedding6 ∘ raw36245step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36245step0 raw36245step0Labels raw36245step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw36246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36246 raw36246Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw36246 raw36246Labels = mixedMoment B raw36246step0 raw36246step0Labels := by
      have hz : ∀ j, raw36246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36246step0 = (fun i j => raw36246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36246step0 raw36246; decide +kernel
      have hl : raw36246step0Labels = raw36246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36246 raw36246Labels permutation434 hz
    mixedMoment B raw36246step0 raw36246step0Labels = mixedMoment B raw36246step1 raw36246step1Labels := by
      have ha : raw36246step1 = (fun i j => raw36246step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36246step1 raw36246step0; decide +kernel
      have hl : raw36246step1Labels = raw36246step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36246step0 raw36246step0Labels permutation56 permutation2
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw36247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw36247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36247 raw36247Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw36247 raw36247Labels = mixedMoment B raw36247step0 raw36247step0Labels := by
      have hz : ∀ j, raw36247 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36247step0 = (fun i j => raw36247 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36247step0 raw36247; decide +kernel
      have hl : raw36247step0Labels = raw36247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36247 raw36247Labels permutation520 hz
    mixedMoment B raw36247step0 raw36247step0Labels = mixedMoment B raw36247step1 raw36247step1Labels := by
      have ha : raw36247step1 = (fun i j => raw36247step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36247step1 raw36247step0; decide +kernel
      have hl : raw36247step1Labels = raw36247step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36247step0 raw36247step0Labels permutation56 permutation2
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw36248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36248step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36248 raw36248Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw36248 raw36248Labels = mixedMoment B raw36248step0 raw36248step0Labels := by
      have ha : raw36248step0 = (fun i j => raw36248 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36248step0 raw36248; decide +kernel
      have hl : raw36248step0Labels = raw36248Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36248 raw36248Labels permutation265 permutation3
    mixedMoment B raw36248step0 raw36248step0Labels = mixedMoment B raw36248step1 raw36248step1Labels := by
      have ha : raw36248step1 = raw36248step0 := by apply Matrix.ext; unfold raw36248step1 raw36248step0; decide +kernel
      have hl : raw36248step0Labels = labelEmbedding6 ∘ raw36248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36248step0 raw36248step0Labels raw36248step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

def raw36249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36249 raw36249Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw36249 raw36249Labels = mixedMoment B raw36249step0 raw36249step0Labels := by
      have hz : ∀ j, raw36249 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36249step0 = (fun i j => raw36249 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36249step0 raw36249; decide +kernel
      have hl : raw36249step0Labels = raw36249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36249 raw36249Labels permutation434 hz
    mixedMoment B raw36249step0 raw36249step0Labels = mixedMoment B raw36249step1 raw36249step1Labels := by
      have ha : raw36249step1 = (fun i j => raw36249step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36249step1 raw36249step0; decide +kernel
      have hl : raw36249step1Labels = raw36249step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36249step0 raw36249step0Labels permutation34 permutation2
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw36250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw36250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36250 raw36250Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw36250 raw36250Labels = mixedMoment B raw36250step0 raw36250step0Labels := by
      have hz : ∀ j, raw36250 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36250step0 = (fun i j => raw36250 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36250step0 raw36250; decide +kernel
      have hl : raw36250step0Labels = raw36250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36250 raw36250Labels permutation520 hz
    mixedMoment B raw36250step0 raw36250step0Labels = mixedMoment B raw36250step1 raw36250step1Labels := by
      have ha : raw36250step1 = (fun i j => raw36250step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36250step1 raw36250step0; decide +kernel
      have hl : raw36250step1Labels = raw36250step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36250step0 raw36250step0Labels permutation34 permutation2
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw36251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36251step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36251step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36251 raw36251Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw36251 raw36251Labels = mixedMoment B raw36251step0 raw36251step0Labels := by
      have ha : raw36251step0 = (fun i j => raw36251 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36251step0 raw36251; decide +kernel
      have hl : raw36251step0Labels = raw36251Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36251 raw36251Labels permutation268 permutation3
    mixedMoment B raw36251step0 raw36251step0Labels = mixedMoment B raw36251step1 raw36251step1Labels := by
      have ha : raw36251step1 = raw36251step0 := by apply Matrix.ext; unfold raw36251step1 raw36251step0; decide +kernel
      have hl : raw36251step0Labels = labelEmbedding6 ∘ raw36251step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36251step0 raw36251step0Labels raw36251step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

def raw36252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36252step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36252step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36252 raw36252Labels = mixedMoment B node5334 node5334Labels := by
  calc
    mixedMoment B raw36252 raw36252Labels = mixedMoment B raw36252step0 raw36252step0Labels := by
      have ha : raw36252step0 = (fun i j => raw36252 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36252step0 raw36252; decide +kernel
      have hl : raw36252step0Labels = raw36252Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36252 raw36252Labels permutation518 permutation3
    mixedMoment B raw36252step0 raw36252step0Labels = mixedMoment B raw36252step1 raw36252step1Labels := by
      have ha : raw36252step1 = -raw36252step0 := by apply Matrix.ext; change ∀ i j, raw36252step1 i j = -(raw36252step0 i j); unfold raw36252step1 raw36252step0; decide +kernel
      have hl : raw36252step1Labels = raw36252step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36252step1 raw36252step1Labels = mixedMoment B raw36252step2 raw36252step2Labels := by
      have ha : raw36252step2 = raw36252step1 := by apply Matrix.ext; unfold raw36252step2 raw36252step1; decide +kernel
      have hl : raw36252step1Labels = labelEmbedding6 ∘ raw36252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36252step1 raw36252step1Labels raw36252step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5334 node5334Labels := by rfl

def raw36253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw36253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36253step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36253step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36253step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36253step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36253 raw36253Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36253 raw36253Labels = mixedMoment B raw36253step0 raw36253step0Labels := by
      have hz : ∀ j, raw36253 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36253step0 = (fun i j => raw36253 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36253step0 raw36253; decide +kernel
      have hl : raw36253step0Labels = raw36253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36253 raw36253Labels permutation520 hz
    mixedMoment B raw36253step0 raw36253step0Labels = mixedMoment B raw36253step1 raw36253step1Labels := by
      have ha : raw36253step1 = (fun i j => raw36253step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36253step1 raw36253step0; decide +kernel
      have hl : raw36253step1Labels = raw36253step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36253step0 raw36253step0Labels permutation126 permutation3
    mixedMoment B raw36253step1 raw36253step1Labels = mixedMoment B raw36253step2 raw36253step2Labels := by
      have ha : raw36253step2 = -raw36253step1 := by apply Matrix.ext; change ∀ i j, raw36253step2 i j = -(raw36253step1 i j); unfold raw36253step2 raw36253step1; decide +kernel
      have hl : raw36253step2Labels = raw36253step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36253step2 raw36253step2Labels = mixedMoment B raw36253step3 raw36253step3Labels := by
      have ha : raw36253step3 = raw36253step2 := by apply Matrix.ext; unfold raw36253step3 raw36253step2; decide +kernel
      have hl : raw36253step2Labels = labelEmbedding6 ∘ raw36253step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36253step2 raw36253step2Labels raw36253step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw36254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36254step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36254 raw36254Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw36254 raw36254Labels = mixedMoment B raw36254step0 raw36254step0Labels := by
      have ha : raw36254step0 = (fun i j => raw36254 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36254step0 raw36254; decide +kernel
      have hl : raw36254step0Labels = raw36254Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36254 raw36254Labels permutation266 permutation3
    mixedMoment B raw36254step0 raw36254step0Labels = mixedMoment B raw36254step1 raw36254step1Labels := by
      have ha : raw36254step1 = raw36254step0 := by apply Matrix.ext; unfold raw36254step1 raw36254step0; decide +kernel
      have hl : raw36254step0Labels = labelEmbedding6 ∘ raw36254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36254step0 raw36254step0Labels raw36254step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

def raw36255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36255step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36255step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36255step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36255 raw36255Labels = mixedMoment B node5334 node5334Labels := by
  calc
    mixedMoment B raw36255 raw36255Labels = mixedMoment B raw36255step0 raw36255step0Labels := by
      have ha : raw36255step0 = (fun i j => raw36255 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36255step0 raw36255; decide +kernel
      have hl : raw36255step0Labels = raw36255Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36255 raw36255Labels permutation588 permutation3
    mixedMoment B raw36255step0 raw36255step0Labels = mixedMoment B raw36255step1 raw36255step1Labels := by
      have ha : raw36255step1 = -raw36255step0 := by apply Matrix.ext; change ∀ i j, raw36255step1 i j = -(raw36255step0 i j); unfold raw36255step1 raw36255step0; decide +kernel
      have hl : raw36255step1Labels = raw36255step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36255step1 raw36255step1Labels = mixedMoment B raw36255step2 raw36255step2Labels := by
      have ha : raw36255step2 = raw36255step1 := by apply Matrix.ext; unfold raw36255step2 raw36255step1; decide +kernel
      have hl : raw36255step1Labels = labelEmbedding6 ∘ raw36255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36255step1 raw36255step1Labels raw36255step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5334 node5334Labels := by rfl

def raw36256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36256step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36256step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36256step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36256step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36256 raw36256Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36256 raw36256Labels = mixedMoment B raw36256step0 raw36256step0Labels := by
      have hz : ∀ j, raw36256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36256step0 = (fun i j => raw36256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36256step0 raw36256; decide +kernel
      have hl : raw36256step0Labels = raw36256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36256 raw36256Labels permutation434 hz
    mixedMoment B raw36256step0 raw36256step0Labels = mixedMoment B raw36256step1 raw36256step1Labels := by
      have ha : raw36256step1 = (fun i j => raw36256step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36256step1 raw36256step0; decide +kernel
      have hl : raw36256step1Labels = raw36256step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36256step0 raw36256step0Labels permutation126 permutation3
    mixedMoment B raw36256step1 raw36256step1Labels = mixedMoment B raw36256step2 raw36256step2Labels := by
      have ha : raw36256step2 = -raw36256step1 := by apply Matrix.ext; change ∀ i j, raw36256step2 i j = -(raw36256step1 i j); unfold raw36256step2 raw36256step1; decide +kernel
      have hl : raw36256step2Labels = raw36256step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36256step2 raw36256step2Labels = mixedMoment B raw36256step3 raw36256step3Labels := by
      have ha : raw36256step3 = raw36256step2 := by apply Matrix.ext; unfold raw36256step3 raw36256step2; decide +kernel
      have hl : raw36256step2Labels = labelEmbedding6 ∘ raw36256step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36256step2 raw36256step2Labels raw36256step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw36257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw36257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36257step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36257 raw36257Labels = mixedMoment B node4927 node4927Labels := by
  calc
    mixedMoment B raw36257 raw36257Labels = mixedMoment B raw36257step0 raw36257step0Labels := by
      have ha : raw36257step0 = (fun i j => raw36257 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36257step0 raw36257; decide +kernel
      have hl : raw36257step0Labels = raw36257Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36257 raw36257Labels permutation265 permutation3
    mixedMoment B raw36257step0 raw36257step0Labels = mixedMoment B raw36257step1 raw36257step1Labels := by
      have ha : raw36257step1 = raw36257step0 := by apply Matrix.ext; unfold raw36257step1 raw36257step0; decide +kernel
      have hl : raw36257step0Labels = labelEmbedding6 ∘ raw36257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36257step0 raw36257step0Labels raw36257step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4927 node4927Labels := by rfl

def raw36258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw36258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36258step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36258step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36258step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36258 raw36258Labels = mixedMoment B node5031 node5031Labels := by
  calc
    mixedMoment B raw36258 raw36258Labels = mixedMoment B raw36258step0 raw36258step0Labels := by
      have ha : raw36258step0 = (fun i j => raw36258 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36258step0 raw36258; decide +kernel
      have hl : raw36258step0Labels = raw36258Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36258 raw36258Labels permutation663 permutation3
    mixedMoment B raw36258step0 raw36258step0Labels = mixedMoment B raw36258step1 raw36258step1Labels := by
      have ha : raw36258step1 = -raw36258step0 := by apply Matrix.ext; change ∀ i j, raw36258step1 i j = -(raw36258step0 i j); unfold raw36258step1 raw36258step0; decide +kernel
      have hl : raw36258step1Labels = raw36258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36258step1 raw36258step1Labels = mixedMoment B raw36258step2 raw36258step2Labels := by
      have ha : raw36258step2 = raw36258step1 := by apply Matrix.ext; unfold raw36258step2 raw36258step1; decide +kernel
      have hl : raw36258step1Labels = labelEmbedding6 ∘ raw36258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36258step1 raw36258step1Labels raw36258step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5031 node5031Labels := by rfl

def raw36259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw36259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36259step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36259step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36259step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36259step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36259 raw36259Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw36259 raw36259Labels = mixedMoment B raw36259step0 raw36259step0Labels := by
      have hz : ∀ j, raw36259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36259step0 = (fun i j => raw36259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36259step0 raw36259; decide +kernel
      have hl : raw36259step0Labels = raw36259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36259 raw36259Labels permutation434 hz
    mixedMoment B raw36259step0 raw36259step0Labels = mixedMoment B raw36259step1 raw36259step1Labels := by
      have ha : raw36259step1 = (fun i j => raw36259step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36259step1 raw36259step0; decide +kernel
      have hl : raw36259step1Labels = raw36259step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36259step0 raw36259step0Labels permutation150 permutation3
    mixedMoment B raw36259step1 raw36259step1Labels = mixedMoment B raw36259step2 raw36259step2Labels := by
      have ha : raw36259step2 = -raw36259step1 := by apply Matrix.ext; change ∀ i j, raw36259step2 i j = -(raw36259step1 i j); unfold raw36259step2 raw36259step1; decide +kernel
      have hl : raw36259step2Labels = raw36259step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36259step2 raw36259step2Labels = mixedMoment B raw36259step3 raw36259step3Labels := by
      have ha : raw36259step3 = raw36259step2 := by apply Matrix.ext; unfold raw36259step3 raw36259step2; decide +kernel
      have hl : raw36259step2Labels = labelEmbedding6 ∘ raw36259step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36259step2 raw36259step2Labels raw36259step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw36260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw36260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36260step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36260step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36260step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36260step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36260 raw36260Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw36260 raw36260Labels = mixedMoment B raw36260step0 raw36260step0Labels := by
      have hz : ∀ j, raw36260 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36260step0 = (fun i j => raw36260 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36260step0 raw36260; decide +kernel
      have hl : raw36260step0Labels = raw36260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36260 raw36260Labels permutation520 hz
    mixedMoment B raw36260step0 raw36260step0Labels = mixedMoment B raw36260step1 raw36260step1Labels := by
      have ha : raw36260step1 = (fun i j => raw36260step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36260step1 raw36260step0; decide +kernel
      have hl : raw36260step1Labels = raw36260step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36260step0 raw36260step0Labels permutation150 permutation3
    mixedMoment B raw36260step1 raw36260step1Labels = mixedMoment B raw36260step2 raw36260step2Labels := by
      have ha : raw36260step2 = -raw36260step1 := by apply Matrix.ext; change ∀ i j, raw36260step2 i j = -(raw36260step1 i j); unfold raw36260step2 raw36260step1; decide +kernel
      have hl : raw36260step2Labels = raw36260step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36260step2 raw36260step2Labels = mixedMoment B raw36260step3 raw36260step3Labels := by
      have ha : raw36260step3 = raw36260step2 := by apply Matrix.ext; unfold raw36260step3 raw36260step2; decide +kernel
      have hl : raw36260step2Labels = labelEmbedding6 ∘ raw36260step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36260step2 raw36260step2Labels raw36260step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw36261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36261 raw36261Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw36261 raw36261Labels = mixedMoment B raw36261step0 raw36261step0Labels := by
      have ha : raw36261step0 = (fun i j => raw36261 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36261step0 raw36261; decide +kernel
      have hl : raw36261step0Labels = raw36261Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36261 raw36261Labels permutation265 permutation3
    _ = mixedMoment B node2556 node2556Labels := by rfl

def raw36262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36262step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36262 raw36262Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw36262 raw36262Labels = mixedMoment B raw36262step0 raw36262step0Labels := by
      have ha : raw36262step0 = (fun i j => raw36262 (permutation289 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36262step0 raw36262; decide +kernel
      have hl : raw36262step0Labels = raw36262Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36262 raw36262Labels permutation289 permutation3
    _ = mixedMoment B node3945 node3945Labels := by rfl

def raw36263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36263 raw36263Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw36263 raw36263Labels = mixedMoment B raw36263step0 raw36263step0Labels := by
      have hz : ∀ j, raw36263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36263step0 = (fun i j => raw36263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36263step0 raw36263; decide +kernel
      have hl : raw36263step0Labels = raw36263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36263 raw36263Labels permutation434 hz
    mixedMoment B raw36263step0 raw36263step0Labels = mixedMoment B raw36263step1 raw36263step1Labels := by
      have ha : raw36263step1 = (fun i j => raw36263step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36263step1 raw36263step0; decide +kernel
      have hl : raw36263step1Labels = raw36263step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36263step0 raw36263step0Labels permutation150 permutation3
    mixedMoment B raw36263step1 raw36263step1Labels = mixedMoment B raw36263step2 raw36263step2Labels := by
      have ha : raw36263step2 = -raw36263step1 := by apply Matrix.ext; change ∀ i j, raw36263step2 i j = -(raw36263step1 i j); unfold raw36263step2 raw36263step1; decide +kernel
      have hl : raw36263step2Labels = raw36263step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw36264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw36264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36264 raw36264Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw36264 raw36264Labels = mixedMoment B raw36264step0 raw36264step0Labels := by
      have hz : ∀ j, raw36264 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36264step0 = (fun i j => raw36264 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36264step0 raw36264; decide +kernel
      have hl : raw36264step0Labels = raw36264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36264 raw36264Labels permutation520 hz
    mixedMoment B raw36264step0 raw36264step0Labels = mixedMoment B raw36264step1 raw36264step1Labels := by
      have ha : raw36264step1 = (fun i j => raw36264step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36264step1 raw36264step0; decide +kernel
      have hl : raw36264step1Labels = raw36264step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36264step0 raw36264step0Labels permutation150 permutation3
    mixedMoment B raw36264step1 raw36264step1Labels = mixedMoment B raw36264step2 raw36264step2Labels := by
      have ha : raw36264step2 = -raw36264step1 := by apply Matrix.ext; change ∀ i j, raw36264step2 i j = -(raw36264step1 i j); unfold raw36264step2 raw36264step1; decide +kernel
      have hl : raw36264step2Labels = raw36264step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw36265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36265 raw36265Labels = mixedMoment B node3992 node3992Labels := by
  calc
    mixedMoment B raw36265 raw36265Labels = mixedMoment B raw36265step0 raw36265step0Labels := by
      have ha : raw36265step0 = (fun i j => raw36265 (permutation269 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36265step0 raw36265; decide +kernel
      have hl : raw36265step0Labels = raw36265Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36265 raw36265Labels permutation269 permutation3
    _ = mixedMoment B node3992 node3992Labels := by rfl

def raw36266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36266 raw36266Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw36266 raw36266Labels = mixedMoment B raw36266step0 raw36266step0Labels := by
      have ha : raw36266step0 = (fun i j => raw36266 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36266step0 raw36266; decide +kernel
      have hl : raw36266step0Labels = raw36266Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36266 raw36266Labels permutation176 permutation3
    _ = mixedMoment B node3945 node3945Labels := by rfl

def raw36267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36267step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36267 raw36267Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw36267 raw36267Labels = mixedMoment B raw36267step0 raw36267step0Labels := by
      have hz : ∀ j, raw36267 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36267step0 = (fun i j => raw36267 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36267step0 raw36267; decide +kernel
      have hl : raw36267step0Labels = raw36267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36267 raw36267Labels permutation434 hz
    mixedMoment B raw36267step0 raw36267step0Labels = mixedMoment B raw36267step1 raw36267step1Labels := by
      have ha : raw36267step1 = (fun i j => raw36267step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36267step1 raw36267step0; decide +kernel
      have hl : raw36267step1Labels = raw36267step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36267step0 raw36267step0Labels permutation151 permutation3
    mixedMoment B raw36267step1 raw36267step1Labels = mixedMoment B raw36267step2 raw36267step2Labels := by
      have ha : raw36267step2 = -raw36267step1 := by apply Matrix.ext; change ∀ i j, raw36267step2 i j = -(raw36267step1 i j); unfold raw36267step2 raw36267step1; decide +kernel
      have hl : raw36267step2Labels = raw36267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw36268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw36268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36268step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36268 raw36268Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw36268 raw36268Labels = mixedMoment B raw36268step0 raw36268step0Labels := by
      have hz : ∀ j, raw36268 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36268step0 = (fun i j => raw36268 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36268step0 raw36268; decide +kernel
      have hl : raw36268step0Labels = raw36268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36268 raw36268Labels permutation520 hz
    mixedMoment B raw36268step0 raw36268step0Labels = mixedMoment B raw36268step1 raw36268step1Labels := by
      have ha : raw36268step1 = (fun i j => raw36268step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36268step1 raw36268step0; decide +kernel
      have hl : raw36268step1Labels = raw36268step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36268step0 raw36268step0Labels permutation151 permutation3
    mixedMoment B raw36268step1 raw36268step1Labels = mixedMoment B raw36268step2 raw36268step2Labels := by
      have ha : raw36268step2 = -raw36268step1 := by apply Matrix.ext; change ∀ i j, raw36268step2 i j = -(raw36268step1 i j); unfold raw36268step2 raw36268step1; decide +kernel
      have hl : raw36268step2Labels = raw36268step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw36269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36269 raw36269Labels = mixedMoment B node2332 node2332Labels := by
  calc
    mixedMoment B raw36269 raw36269Labels = mixedMoment B raw36269step0 raw36269step0Labels := by
      have ha : raw36269step0 = (fun i j => raw36269 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36269step0 raw36269; decide +kernel
      have hl : raw36269step0Labels = raw36269Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36269 raw36269Labels permutation152 permutation3
    _ = mixedMoment B node2332 node2332Labels := by rfl

def raw36270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36270 raw36270Labels = mixedMoment B node2332 node2332Labels := by
  calc
    mixedMoment B raw36270 raw36270Labels = mixedMoment B raw36270step0 raw36270step0Labels := by
      have ha : raw36270step0 = (fun i j => raw36270 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36270step0 raw36270; decide +kernel
      have hl : raw36270step0Labels = raw36270Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36270 raw36270Labels permutation265 permutation3
    _ = mixedMoment B node2332 node2332Labels := by rfl

def raw36271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36271step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36271 raw36271Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw36271 raw36271Labels = mixedMoment B raw36271step0 raw36271step0Labels := by
      have hz : ∀ j, raw36271 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36271step0 = (fun i j => raw36271 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36271step0 raw36271; decide +kernel
      have hl : raw36271step0Labels = raw36271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36271 raw36271Labels permutation434 hz
    mixedMoment B raw36271step0 raw36271step0Labels = mixedMoment B raw36271step1 raw36271step1Labels := by
      have ha : raw36271step1 = (fun i j => raw36271step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36271step1 raw36271step0; decide +kernel
      have hl : raw36271step1Labels = raw36271step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36271step0 raw36271step0Labels permutation32 permutation3
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw36272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw36272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36272step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36272 raw36272Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw36272 raw36272Labels = mixedMoment B raw36272step0 raw36272step0Labels := by
      have hz : ∀ j, raw36272 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36272step0 = (fun i j => raw36272 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36272step0 raw36272; decide +kernel
      have hl : raw36272step0Labels = raw36272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36272 raw36272Labels permutation520 hz
    mixedMoment B raw36272step0 raw36272step0Labels = mixedMoment B raw36272step1 raw36272step1Labels := by
      have ha : raw36272step1 = (fun i j => raw36272step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36272step1 raw36272step0; decide +kernel
      have hl : raw36272step1Labels = raw36272step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36272step0 raw36272step0Labels permutation32 permutation3
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw36273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36273step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36273 raw36273Labels = mixedMoment B node3930 node3930Labels := by
  calc
    mixedMoment B raw36273 raw36273Labels = mixedMoment B raw36273step0 raw36273step0Labels := by
      have ha : raw36273step0 = (fun i j => raw36273 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36273step0 raw36273; decide +kernel
      have hl : raw36273step0Labels = raw36273Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36273 raw36273Labels permutation156 permutation3
    _ = mixedMoment B node3930 node3930Labels := by rfl

def raw36274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36274 raw36274Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw36274 raw36274Labels = mixedMoment B raw36274step0 raw36274step0Labels := by
      have ha : raw36274step0 = (fun i j => raw36274 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36274step0 raw36274; decide +kernel
      have hl : raw36274step0Labels = raw36274Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36274 raw36274Labels permutation155 permutation3
    _ = mixedMoment B node2318 node2318Labels := by rfl

def raw36275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36275 raw36275Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw36275 raw36275Labels = mixedMoment B raw36275step0 raw36275step0Labels := by
      have ha : raw36275step0 = (fun i j => raw36275 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36275step0 raw36275; decide +kernel
      have hl : raw36275step0Labels = raw36275Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36275 raw36275Labels permutation268 permutation3
    _ = mixedMoment B node2318 node2318Labels := by rfl

def raw36276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36276 raw36276Labels = mixedMoment B node3669 node3669Labels := by
  calc
    mixedMoment B raw36276 raw36276Labels = mixedMoment B raw36276step0 raw36276step0Labels := by
      have ha : raw36276step0 = (fun i j => raw36276 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36276step0 raw36276; decide +kernel
      have hl : raw36276step0Labels = raw36276Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36276 raw36276Labels permutation518 permutation3
    mixedMoment B raw36276step0 raw36276step0Labels = mixedMoment B raw36276step1 raw36276step1Labels := by
      have ha : raw36276step1 = -raw36276step0 := by apply Matrix.ext; change ∀ i j, raw36276step1 i j = -(raw36276step0 i j); unfold raw36276step1 raw36276step0; decide +kernel
      have hl : raw36276step1Labels = raw36276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3669 node3669Labels := by rfl

def raw36277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw36277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36277 raw36277Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw36277 raw36277Labels = mixedMoment B raw36277step0 raw36277step0Labels := by
      have hz : ∀ j, raw36277 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36277step0 = (fun i j => raw36277 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36277step0 raw36277; decide +kernel
      have hl : raw36277step0Labels = raw36277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36277 raw36277Labels permutation520 hz
    mixedMoment B raw36277step0 raw36277step0Labels = mixedMoment B raw36277step1 raw36277step1Labels := by
      have ha : raw36277step1 = (fun i j => raw36277step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36277step1 raw36277step0; decide +kernel
      have hl : raw36277step1Labels = raw36277step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36277step0 raw36277step0Labels permutation126 permutation3
    mixedMoment B raw36277step1 raw36277step1Labels = mixedMoment B raw36277step2 raw36277step2Labels := by
      have ha : raw36277step2 = -raw36277step1 := by apply Matrix.ext; change ∀ i j, raw36277step2 i j = -(raw36277step1 i j); unfold raw36277step2 raw36277step1; decide +kernel
      have hl : raw36277step2Labels = raw36277step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3694 node3694Labels := by rfl

def raw36278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36278 raw36278Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw36278 raw36278Labels = mixedMoment B raw36278step0 raw36278step0Labels := by
      have ha : raw36278step0 = (fun i j => raw36278 (permutation503 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36278step0 raw36278; decide +kernel
      have hl : raw36278step0Labels = raw36278Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36278 raw36278Labels permutation503 permutation3
    mixedMoment B raw36278step0 raw36278step0Labels = mixedMoment B raw36278step1 raw36278step1Labels := by
      have ha : raw36278step1 = -raw36278step0 := by apply Matrix.ext; change ∀ i j, raw36278step1 i j = -(raw36278step0 i j); unfold raw36278step1 raw36278step0; decide +kernel
      have hl : raw36278step1Labels = raw36278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3779 node3779Labels := by rfl

def raw36279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36279 raw36279Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw36279 raw36279Labels = mixedMoment B raw36279step0 raw36279step0Labels := by
      have ha : raw36279step0 = (fun i j => raw36279 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36279step0 raw36279; decide +kernel
      have hl : raw36279step0Labels = raw36279Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36279 raw36279Labels permutation153 permutation3
    _ = mixedMoment B node2318 node2318Labels := by rfl

def raw36280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36280step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36280 raw36280Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw36280 raw36280Labels = mixedMoment B raw36280step0 raw36280step0Labels := by
      have ha : raw36280step0 = (fun i j => raw36280 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36280step0 raw36280; decide +kernel
      have hl : raw36280step0Labels = raw36280Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36280 raw36280Labels permutation266 permutation3
    _ = mixedMoment B node2318 node2318Labels := by rfl

def raw36281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36281step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36281 raw36281Labels = mixedMoment B node3669 node3669Labels := by
  calc
    mixedMoment B raw36281 raw36281Labels = mixedMoment B raw36281step0 raw36281step0Labels := by
      have ha : raw36281step0 = (fun i j => raw36281 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36281step0 raw36281; decide +kernel
      have hl : raw36281step0Labels = raw36281Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36281 raw36281Labels permutation588 permutation3
    mixedMoment B raw36281step0 raw36281step0Labels = mixedMoment B raw36281step1 raw36281step1Labels := by
      have ha : raw36281step1 = -raw36281step0 := by apply Matrix.ext; change ∀ i j, raw36281step1 i j = -(raw36281step0 i j); unfold raw36281step1 raw36281step0; decide +kernel
      have hl : raw36281step1Labels = raw36281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3669 node3669Labels := by rfl

def raw36282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36282step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36282step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36282 raw36282Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw36282 raw36282Labels = mixedMoment B raw36282step0 raw36282step0Labels := by
      have hz : ∀ j, raw36282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36282step0 = (fun i j => raw36282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36282step0 raw36282; decide +kernel
      have hl : raw36282step0Labels = raw36282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36282 raw36282Labels permutation434 hz
    mixedMoment B raw36282step0 raw36282step0Labels = mixedMoment B raw36282step1 raw36282step1Labels := by
      have ha : raw36282step1 = (fun i j => raw36282step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36282step1 raw36282step0; decide +kernel
      have hl : raw36282step1Labels = raw36282step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36282step0 raw36282step0Labels permutation126 permutation3
    mixedMoment B raw36282step1 raw36282step1Labels = mixedMoment B raw36282step2 raw36282step2Labels := by
      have ha : raw36282step2 = -raw36282step1 := by apply Matrix.ext; change ∀ i j, raw36282step2 i j = -(raw36282step1 i j); unfold raw36282step2 raw36282step1; decide +kernel
      have hl : raw36282step2Labels = raw36282step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3694 node3694Labels := by rfl

def raw36283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw36283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36283step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36283 raw36283Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw36283 raw36283Labels = mixedMoment B raw36283step0 raw36283step0Labels := by
      have ha : raw36283step0 = (fun i j => raw36283 (permutation567 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36283step0 raw36283; decide +kernel
      have hl : raw36283step0Labels = raw36283Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36283 raw36283Labels permutation567 permutation3
    mixedMoment B raw36283step0 raw36283step0Labels = mixedMoment B raw36283step1 raw36283step1Labels := by
      have ha : raw36283step1 = -raw36283step0 := by apply Matrix.ext; change ∀ i j, raw36283step1 i j = -(raw36283step0 i j); unfold raw36283step1 raw36283step0; decide +kernel
      have hl : raw36283step1Labels = raw36283step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3779 node3779Labels := by rfl

def raw36284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw36284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36284step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36284 raw36284Labels = mixedMoment B node2317 node2317Labels := by
  calc
    mixedMoment B raw36284 raw36284Labels = mixedMoment B raw36284step0 raw36284step0Labels := by
      have ha : raw36284step0 = (fun i j => raw36284 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36284step0 raw36284; decide +kernel
      have hl : raw36284step0Labels = raw36284Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36284 raw36284Labels permutation152 permutation3
    _ = mixedMoment B node2317 node2317Labels := by rfl

def raw36285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw36285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36285step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36285 raw36285Labels = mixedMoment B node2317 node2317Labels := by
  calc
    mixedMoment B raw36285 raw36285Labels = mixedMoment B raw36285step0 raw36285step0Labels := by
      have ha : raw36285step0 = (fun i j => raw36285 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36285step0 raw36285; decide +kernel
      have hl : raw36285step0Labels = raw36285Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36285 raw36285Labels permutation265 permutation3
    _ = mixedMoment B node2317 node2317Labels := by rfl

def raw36286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw36286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36286step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36286 raw36286Labels = mixedMoment B node2420 node2420Labels := by
  calc
    mixedMoment B raw36286 raw36286Labels = mixedMoment B raw36286step0 raw36286step0Labels := by
      have ha : raw36286step0 = (fun i j => raw36286 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36286step0 raw36286; decide +kernel
      have hl : raw36286step0Labels = raw36286Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36286 raw36286Labels permutation663 permutation3
    mixedMoment B raw36286step0 raw36286step0Labels = mixedMoment B raw36286step1 raw36286step1Labels := by
      have ha : raw36286step1 = -raw36286step0 := by apply Matrix.ext; change ∀ i j, raw36286step1 i j = -(raw36286step0 i j); unfold raw36286step1 raw36286step0; decide +kernel
      have hl : raw36286step1Labels = raw36286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2420 node2420Labels := by rfl

def raw36287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw36287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36287 raw36287Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw36287 raw36287Labels = mixedMoment B raw36287step0 raw36287step0Labels := by
      have hz : ∀ j, raw36287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36287step0 = (fun i j => raw36287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36287step0 raw36287; decide +kernel
      have hl : raw36287step0Labels = raw36287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36287 raw36287Labels permutation434 hz
    mixedMoment B raw36287step0 raw36287step0Labels = mixedMoment B raw36287step1 raw36287step1Labels := by
      have ha : raw36287step1 = (fun i j => raw36287step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36287step1 raw36287step0; decide +kernel
      have hl : raw36287step1Labels = raw36287step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36287step0 raw36287step0Labels permutation150 permutation3
    mixedMoment B raw36287step1 raw36287step1Labels = mixedMoment B raw36287step2 raw36287step2Labels := by
      have ha : raw36287step2 = -raw36287step1 := by apply Matrix.ext; change ∀ i j, raw36287step2 i j = -(raw36287step1 i j); unfold raw36287step2 raw36287step1; decide +kernel
      have hl : raw36287step2Labels = raw36287step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw36288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw36288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36288 raw36288Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw36288 raw36288Labels = mixedMoment B raw36288step0 raw36288step0Labels := by
      have hz : ∀ j, raw36288 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36288step0 = (fun i j => raw36288 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36288step0 raw36288; decide +kernel
      have hl : raw36288step0Labels = raw36288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36288 raw36288Labels permutation520 hz
    mixedMoment B raw36288step0 raw36288step0Labels = mixedMoment B raw36288step1 raw36288step1Labels := by
      have ha : raw36288step1 = (fun i j => raw36288step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36288step1 raw36288step0; decide +kernel
      have hl : raw36288step1Labels = raw36288step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36288step0 raw36288step0Labels permutation150 permutation3
    mixedMoment B raw36288step1 raw36288step1Labels = mixedMoment B raw36288step2 raw36288step2Labels := by
      have ha : raw36288step2 = -raw36288step1 := by apply Matrix.ext; change ∀ i j, raw36288step2 i j = -(raw36288step1 i j); unfold raw36288step2 raw36288step1; decide +kernel
      have hl : raw36288step2Labels = raw36288step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw36289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36289step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36289 raw36289Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw36289 raw36289Labels = mixedMoment B raw36289step0 raw36289step0Labels := by
      have ha : raw36289step0 = (fun i j => raw36289 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36289step0 raw36289; decide +kernel
      have hl : raw36289step0Labels = raw36289Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36289 raw36289Labels permutation265 permutation3
    mixedMoment B raw36289step0 raw36289step0Labels = mixedMoment B raw36289step1 raw36289step1Labels := by
      have ha : raw36289step1 = raw36289step0 := by apply Matrix.ext; unfold raw36289step1 raw36289step0; decide +kernel
      have hl : raw36289step0Labels = labelEmbedding6 ∘ raw36289step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36289step0 raw36289step0Labels raw36289step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw36290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36290 raw36290Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw36290 raw36290Labels = mixedMoment B raw36290step0 raw36290step0Labels := by
      have ha : raw36290step0 = (fun i j => raw36290 (permutation660 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36290step0 raw36290; decide +kernel
      have hl : raw36290step0Labels = raw36290Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36290 raw36290Labels permutation660 permutation2
    mixedMoment B raw36290step0 raw36290step0Labels = mixedMoment B raw36290step1 raw36290step1Labels := by
      have ha : raw36290step1 = -raw36290step0 := by apply Matrix.ext; change ∀ i j, raw36290step1 i j = -(raw36290step0 i j); unfold raw36290step1 raw36290step0; decide +kernel
      have hl : raw36290step1Labels = raw36290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5396 node5396Labels := by rfl

def raw36291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36291 raw36291Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw36291 raw36291Labels = mixedMoment B raw36291step0 raw36291step0Labels := by
      have ha : raw36291step0 = (fun i j => raw36291 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36291step0 raw36291; decide +kernel
      have hl : raw36291step0Labels = raw36291Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36291 raw36291Labels permutation687 permutation2
    mixedMoment B raw36291step0 raw36291step0Labels = mixedMoment B raw36291step1 raw36291step1Labels := by
      have ha : raw36291step1 = -raw36291step0 := by apply Matrix.ext; change ∀ i j, raw36291step1 i j = -(raw36291step0 i j); unfold raw36291step1 raw36291step0; decide +kernel
      have hl : raw36291step1Labels = raw36291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw36292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36292step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36292 raw36292Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw36292 raw36292Labels = mixedMoment B raw36292step0 raw36292step0Labels := by
      have hz : ∀ j, raw36292 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36292step0 = (fun i j => raw36292 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36292step0 raw36292; decide +kernel
      have hl : raw36292step0Labels = raw36292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36292 raw36292Labels permutation520 hz
    mixedMoment B raw36292step0 raw36292step0Labels = mixedMoment B raw36292step1 raw36292step1Labels := by
      have ha : raw36292step1 = (fun i j => raw36292step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36292step1 raw36292step0; decide +kernel
      have hl : raw36292step1Labels = raw36292step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36292step0 raw36292step0Labels permutation150 permutation2
    mixedMoment B raw36292step1 raw36292step1Labels = mixedMoment B raw36292step2 raw36292step2Labels := by
      have ha : raw36292step2 = -raw36292step1 := by apply Matrix.ext; change ∀ i j, raw36292step2 i j = -(raw36292step1 i j); unfold raw36292step2 raw36292step1; decide +kernel
      have hl : raw36292step2Labels = raw36292step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw36293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36293 raw36293Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw36293 raw36293Labels = mixedMoment B raw36293step0 raw36293step0Labels := by
      have ha : raw36293step0 = (fun i j => raw36293 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36293step0 raw36293; decide +kernel
      have hl : raw36293step0Labels = raw36293Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36293 raw36293Labels permutation267 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw36294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36294step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36294 raw36294Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw36294 raw36294Labels = mixedMoment B raw36294step0 raw36294step0Labels := by
      have ha : raw36294step0 = (fun i j => raw36294 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36294step0 raw36294; decide +kernel
      have hl : raw36294step0Labels = raw36294Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36294 raw36294Labels permutation152 permutation3
    mixedMoment B raw36294step0 raw36294step0Labels = mixedMoment B raw36294step1 raw36294step1Labels := by
      have ha : raw36294step1 = raw36294step0 := by apply Matrix.ext; unfold raw36294step1 raw36294step0; decide +kernel
      have hl : raw36294step0Labels = labelEmbedding6 ∘ raw36294step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36294step0 raw36294step0Labels raw36294step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw36295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36295step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36295 raw36295Labels = mixedMoment B node4942 node4942Labels := by
  calc
    mixedMoment B raw36295 raw36295Labels = mixedMoment B raw36295step0 raw36295step0Labels := by
      have ha : raw36295step0 = (fun i j => raw36295 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36295step0 raw36295; decide +kernel
      have hl : raw36295step0Labels = raw36295Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36295 raw36295Labels permutation273 permutation3
    mixedMoment B raw36295step0 raw36295step0Labels = mixedMoment B raw36295step1 raw36295step1Labels := by
      have ha : raw36295step1 = raw36295step0 := by apply Matrix.ext; unfold raw36295step1 raw36295step0; decide +kernel
      have hl : raw36295step0Labels = labelEmbedding6 ∘ raw36295step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36295step0 raw36295step0Labels raw36295step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4942 node4942Labels := by rfl

def raw36296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36296 raw36296Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw36296 raw36296Labels = mixedMoment B raw36296step0 raw36296step0Labels := by
      have ha : raw36296step0 = (fun i j => raw36296 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36296step0 raw36296; decide +kernel
      have hl : raw36296step0Labels = raw36296Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36296 raw36296Labels permutation681 permutation2
    mixedMoment B raw36296step0 raw36296step0Labels = mixedMoment B raw36296step1 raw36296step1Labels := by
      have ha : raw36296step1 = -raw36296step0 := by apply Matrix.ext; change ∀ i j, raw36296step1 i j = -(raw36296step0 i j); unfold raw36296step1 raw36296step0; decide +kernel
      have hl : raw36296step1Labels = raw36296step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5419 node5419Labels := by rfl

def raw36297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36297step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36297 raw36297Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw36297 raw36297Labels = mixedMoment B raw36297step0 raw36297step0Labels := by
      have hz : ∀ j, raw36297 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36297step0 = (fun i j => raw36297 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36297step0 raw36297; decide +kernel
      have hl : raw36297step0Labels = raw36297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36297 raw36297Labels permutation520 hz
    mixedMoment B raw36297step0 raw36297step0Labels = mixedMoment B raw36297step1 raw36297step1Labels := by
      have ha : raw36297step1 = (fun i j => raw36297step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36297step1 raw36297step0; decide +kernel
      have hl : raw36297step1Labels = raw36297step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36297step0 raw36297step0Labels permutation150 permutation2
    mixedMoment B raw36297step1 raw36297step1Labels = mixedMoment B raw36297step2 raw36297step2Labels := by
      have ha : raw36297step2 = -raw36297step1 := by apply Matrix.ext; change ∀ i j, raw36297step2 i j = -(raw36297step1 i j); unfold raw36297step2 raw36297step1; decide +kernel
      have hl : raw36297step2Labels = raw36297step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw36298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36298 raw36298Labels = mixedMoment B node5461 node5461Labels := by
  calc
    mixedMoment B raw36298 raw36298Labels = mixedMoment B raw36298step0 raw36298step0Labels := by
      have ha : raw36298step0 = (fun i j => raw36298 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36298step0 raw36298; decide +kernel
      have hl : raw36298step0Labels = raw36298Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36298 raw36298Labels permutation154 permutation2
    _ = mixedMoment B node5461 node5461Labels := by rfl

def raw36299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36299step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36299step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36299 raw36299Labels = mixedMoment B node4933 node4933Labels := by
  calc
    mixedMoment B raw36299 raw36299Labels = mixedMoment B raw36299step0 raw36299step0Labels := by
      have ha : raw36299step0 = (fun i j => raw36299 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36299step0 raw36299; decide +kernel
      have hl : raw36299step0Labels = raw36299Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36299 raw36299Labels permutation268 permutation3
    mixedMoment B raw36299step0 raw36299step0Labels = mixedMoment B raw36299step1 raw36299step1Labels := by
      have ha : raw36299step1 = raw36299step0 := by apply Matrix.ext; unfold raw36299step1 raw36299step0; decide +kernel
      have hl : raw36299step0Labels = labelEmbedding6 ∘ raw36299step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36299step0 raw36299step0Labels raw36299step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4933 node4933Labels := by rfl

def raw36300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36300 raw36300Labels = mixedMoment B node5337 node5337Labels := by
  calc
    mixedMoment B raw36300 raw36300Labels = mixedMoment B raw36300step0 raw36300step0Labels := by
      have ha : raw36300step0 = (fun i j => raw36300 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36300step0 raw36300; decide +kernel
      have hl : raw36300step0Labels = raw36300Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36300 raw36300Labels permutation663 permutation2
    mixedMoment B raw36300step0 raw36300step0Labels = mixedMoment B raw36300step1 raw36300step1Labels := by
      have ha : raw36300step1 = -raw36300step0 := by apply Matrix.ext; change ∀ i j, raw36300step1 i j = -(raw36300step0 i j); unfold raw36300step1 raw36300step0; decide +kernel
      have hl : raw36300step1Labels = raw36300step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5337 node5337Labels := by rfl

def raw36301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36301step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36301 raw36301Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36301 raw36301Labels = mixedMoment B raw36301step0 raw36301step0Labels := by
      have hz : ∀ j, raw36301 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36301step0 = (fun i j => raw36301 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36301step0 raw36301; decide +kernel
      have hl : raw36301step0Labels = raw36301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36301 raw36301Labels permutation520 hz
    mixedMoment B raw36301step0 raw36301step0Labels = mixedMoment B raw36301step1 raw36301step1Labels := by
      have ha : raw36301step1 = (fun i j => raw36301step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36301step1 raw36301step0; decide +kernel
      have hl : raw36301step1Labels = raw36301step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36301step0 raw36301step0Labels permutation150 permutation2
    mixedMoment B raw36301step1 raw36301step1Labels = mixedMoment B raw36301step2 raw36301step2Labels := by
      have ha : raw36301step2 = -raw36301step1 := by apply Matrix.ext; change ∀ i j, raw36301step2 i j = -(raw36301step1 i j); unfold raw36301step2 raw36301step1; decide +kernel
      have hl : raw36301step2Labels = raw36301step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw36302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36302 raw36302Labels = mixedMoment B node5459 node5459Labels := by
  calc
    mixedMoment B raw36302 raw36302Labels = mixedMoment B raw36302step0 raw36302step0Labels := by
      have ha : raw36302step0 = (fun i j => raw36302 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36302step0 raw36302; decide +kernel
      have hl : raw36302step0Labels = raw36302Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36302 raw36302Labels permutation155 permutation2
    _ = mixedMoment B node5459 node5459Labels := by rfl

def raw36303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36303step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36303step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36303step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36303 raw36303Labels = mixedMoment B node4931 node4931Labels := by
  calc
    mixedMoment B raw36303 raw36303Labels = mixedMoment B raw36303step0 raw36303step0Labels := by
      have ha : raw36303step0 = (fun i j => raw36303 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36303step0 raw36303; decide +kernel
      have hl : raw36303step0Labels = raw36303Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36303 raw36303Labels permutation266 permutation3
    mixedMoment B raw36303step0 raw36303step0Labels = mixedMoment B raw36303step1 raw36303step1Labels := by
      have ha : raw36303step1 = raw36303step0 := by apply Matrix.ext; unfold raw36303step1 raw36303step0; decide +kernel
      have hl : raw36303step0Labels = labelEmbedding6 ∘ raw36303step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36303step0 raw36303step0Labels raw36303step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4931 node4931Labels := by rfl

def raw36304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36304 raw36304Labels = mixedMoment B node5373 node5373Labels := by
  calc
    mixedMoment B raw36304 raw36304Labels = mixedMoment B raw36304step0 raw36304step0Labels := by
      have ha : raw36304step0 = (fun i j => raw36304 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36304step0 raw36304; decide +kernel
      have hl : raw36304step0Labels = raw36304Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36304 raw36304Labels permutation687 permutation2
    mixedMoment B raw36304step0 raw36304step0Labels = mixedMoment B raw36304step1 raw36304step1Labels := by
      have ha : raw36304step1 = -raw36304step0 := by apply Matrix.ext; change ∀ i j, raw36304step1 i j = -(raw36304step0 i j); unfold raw36304step1 raw36304step0; decide +kernel
      have hl : raw36304step1Labels = raw36304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5373 node5373Labels := by rfl

def raw36305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36305 raw36305Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw36305 raw36305Labels = mixedMoment B raw36305step0 raw36305step0Labels := by
      have ha : raw36305step0 = (fun i j => raw36305 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36305step0 raw36305; decide +kernel
      have hl : raw36305step0Labels = raw36305Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36305 raw36305Labels permutation687 permutation2
    mixedMoment B raw36305step0 raw36305step0Labels = mixedMoment B raw36305step1 raw36305step1Labels := by
      have ha : raw36305step1 = -raw36305step0 := by apply Matrix.ext; change ∀ i j, raw36305step1 i j = -(raw36305step0 i j); unfold raw36305step1 raw36305step0; decide +kernel
      have hl : raw36305step1Labels = raw36305step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5377 node5377Labels := by rfl

def raw36306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36306step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36306step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36306step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36306step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36306step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36306 raw36306Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw36306 raw36306Labels = mixedMoment B raw36306step0 raw36306step0Labels := by
      have ha : raw36306step0 = (fun i j => raw36306 (permutation567 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36306step0 raw36306; decide +kernel
      have hl : raw36306step0Labels = raw36306Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36306 raw36306Labels permutation567 permutation3
    mixedMoment B raw36306step0 raw36306step0Labels = mixedMoment B raw36306step1 raw36306step1Labels := by
      have ha : raw36306step1 = -raw36306step0 := by apply Matrix.ext; change ∀ i j, raw36306step1 i j = -(raw36306step0 i j); unfold raw36306step1 raw36306step0; decide +kernel
      have hl : raw36306step1Labels = raw36306step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36306step1 raw36306step1Labels = mixedMoment B raw36306step2 raw36306step2Labels := by
      have ha : raw36306step2 = raw36306step1 := by apply Matrix.ext; unfold raw36306step2 raw36306step1; decide +kernel
      have hl : raw36306step1Labels = labelEmbedding6 ∘ raw36306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36306step1 raw36306step1Labels raw36306step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5419 node5419Labels := by rfl

def raw36307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36307step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36307step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36307 raw36307Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw36307 raw36307Labels = mixedMoment B raw36307step0 raw36307step0Labels := by
      have ha : raw36307step0 = (fun i j => raw36307 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36307step0 raw36307; decide +kernel
      have hl : raw36307step0Labels = raw36307Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36307 raw36307Labels permutation265 permutation3
    mixedMoment B raw36307step0 raw36307step0Labels = mixedMoment B raw36307step1 raw36307step1Labels := by
      have ha : raw36307step1 = raw36307step0 := by apply Matrix.ext; unfold raw36307step1 raw36307step0; decide +kernel
      have hl : raw36307step0Labels = labelEmbedding6 ∘ raw36307step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36307step0 raw36307step0Labels raw36307step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4930 node4930Labels := by rfl

def raw36308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36308 raw36308Labels = mixedMoment B node5039 node5039Labels := by
  calc
    mixedMoment B raw36308 raw36308Labels = mixedMoment B raw36308step0 raw36308step0Labels := by
      have ha : raw36308step0 = (fun i j => raw36308 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36308step0 raw36308; decide +kernel
      have hl : raw36308step0Labels = raw36308Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36308 raw36308Labels permutation663 permutation2
    mixedMoment B raw36308step0 raw36308step0Labels = mixedMoment B raw36308step1 raw36308step1Labels := by
      have ha : raw36308step1 = -raw36308step0 := by apply Matrix.ext; change ∀ i j, raw36308step1 i j = -(raw36308step0 i j); unfold raw36308step1 raw36308step0; decide +kernel
      have hl : raw36308step1Labels = raw36308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5039 node5039Labels := by rfl

def raw36309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36309step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36309 raw36309Labels = mixedMoment B node5130 node5130Labels := by
  calc
    mixedMoment B raw36309 raw36309Labels = mixedMoment B raw36309step0 raw36309step0Labels := by
      have ha : raw36309step0 = (fun i j => raw36309 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36309step0 raw36309; decide +kernel
      have hl : raw36309step0Labels = raw36309Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36309 raw36309Labels permutation687 permutation2
    mixedMoment B raw36309step0 raw36309step0Labels = mixedMoment B raw36309step1 raw36309step1Labels := by
      have ha : raw36309step1 = -raw36309step0 := by apply Matrix.ext; change ∀ i j, raw36309step1 i j = -(raw36309step0 i j); unfold raw36309step1 raw36309step0; decide +kernel
      have hl : raw36309step1Labels = raw36309step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5130 node5130Labels := by rfl

def raw36310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw36310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw36310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36310step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36310 raw36310Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw36310 raw36310Labels = mixedMoment B raw36310step0 raw36310step0Labels := by
      have hz : ∀ j, raw36310 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36310step0 = (fun i j => raw36310 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36310step0 raw36310; decide +kernel
      have hl : raw36310step0Labels = raw36310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36310 raw36310Labels permutation520 hz
    mixedMoment B raw36310step0 raw36310step0Labels = mixedMoment B raw36310step1 raw36310step1Labels := by
      have ha : raw36310step1 = (fun i j => raw36310step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36310step1 raw36310step0; decide +kernel
      have hl : raw36310step1Labels = raw36310step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36310step0 raw36310step0Labels permutation150 permutation2
    mixedMoment B raw36310step1 raw36310step1Labels = mixedMoment B raw36310step2 raw36310step2Labels := by
      have ha : raw36310step2 = -raw36310step1 := by apply Matrix.ext; change ∀ i j, raw36310step2 i j = -(raw36310step1 i j); unfold raw36310step2 raw36310step1; decide +kernel
      have hl : raw36310step2Labels = raw36310step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw36311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw36311step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36311step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36311step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36311 raw36311Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw36311 raw36311Labels = mixedMoment B raw36311step0 raw36311step0Labels := by
      have ha : raw36311step0 = (fun i j => raw36311 (permutation275 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36311step0 raw36311; decide +kernel
      have hl : raw36311step0Labels = raw36311Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36311 raw36311Labels permutation275 permutation5
    mixedMoment B raw36311step0 raw36311step0Labels = mixedMoment B raw36311step1 raw36311step1Labels := by
      have ha : raw36311step1 = -raw36311step0 := by apply Matrix.ext; change ∀ i j, raw36311step1 i j = -(raw36311step0 i j); unfold raw36311step1 raw36311step0; decide +kernel
      have hl : raw36311step1Labels = raw36311step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36311step1 raw36311step1Labels = mixedMoment B raw36311step2 raw36311step2Labels := by
      have ha : raw36311step2 = raw36311step1 := by apply Matrix.ext; unfold raw36311step2 raw36311step1; decide +kernel
      have hl : raw36311step1Labels = labelEmbedding1 ∘ raw36311step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36311step1 raw36311step1Labels raw36311step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw36312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36312 raw36312Labels = mixedMoment B node3798 node3798Labels := by
  calc
    mixedMoment B raw36312 raw36312Labels = mixedMoment B raw36312step0 raw36312step0Labels := by
      have ha : raw36312step0 = (fun i j => raw36312 (permutation660 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36312step0 raw36312; decide +kernel
      have hl : raw36312step0Labels = raw36312Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36312 raw36312Labels permutation660 permutation7
    mixedMoment B raw36312step0 raw36312step0Labels = mixedMoment B raw36312step1 raw36312step1Labels := by
      have ha : raw36312step1 = raw36312step0 := by apply Matrix.ext; unfold raw36312step1 raw36312step0; decide +kernel
      have hl : raw36312step0Labels = labelEmbedding1 ∘ raw36312step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36312step0 raw36312step0Labels raw36312step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3798 node3798Labels := by rfl

def raw36313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36313step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36313step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36313 raw36313Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw36313 raw36313Labels = mixedMoment B raw36313step0 raw36313step0Labels := by
      have ha : raw36313step0 = (fun i j => raw36313 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36313step0 raw36313; decide +kernel
      have hl : raw36313step0Labels = raw36313Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36313 raw36313Labels permutation663 permutation7
    mixedMoment B raw36313step0 raw36313step0Labels = mixedMoment B raw36313step1 raw36313step1Labels := by
      have ha : raw36313step1 = raw36313step0 := by apply Matrix.ext; unfold raw36313step1 raw36313step0; decide +kernel
      have hl : raw36313step0Labels = labelEmbedding1 ∘ raw36313step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36313step0 raw36313step0Labels raw36313step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw36314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36314step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36314 raw36314Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw36314 raw36314Labels = mixedMoment B raw36314step0 raw36314step0Labels := by
      have hz : ∀ j, raw36314 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36314step0 = (fun i j => raw36314 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36314step0 raw36314; decide +kernel
      have hl : raw36314step0Labels = raw36314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36314 raw36314Labels permutation520 hz
    mixedMoment B raw36314step0 raw36314step0Labels = mixedMoment B raw36314step1 raw36314step1Labels := by
      have ha : raw36314step1 = (fun i j => raw36314step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36314step1 raw36314step0; decide +kernel
      have hl : raw36314step1Labels = raw36314step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36314step0 raw36314step0Labels permutation150 permutation7
    mixedMoment B raw36314step1 raw36314step1Labels = mixedMoment B raw36314step2 raw36314step2Labels := by
      have ha : raw36314step2 = raw36314step1 := by apply Matrix.ext; unfold raw36314step2 raw36314step1; decide +kernel
      have hl : raw36314step1Labels = labelEmbedding1 ∘ raw36314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36314step1 raw36314step1Labels raw36314step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw36315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36315step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36315 raw36315Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw36315 raw36315Labels = mixedMoment B raw36315step0 raw36315step0Labels := by
      have ha : raw36315step0 = (fun i j => raw36315 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36315step0 raw36315; decide +kernel
      have hl : raw36315step0Labels = raw36315Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36315 raw36315Labels permutation663 permutation7
    mixedMoment B raw36315step0 raw36315step0Labels = mixedMoment B raw36315step1 raw36315step1Labels := by
      have ha : raw36315step1 = raw36315step0 := by apply Matrix.ext; unfold raw36315step1 raw36315step0; decide +kernel
      have hl : raw36315step0Labels = labelEmbedding1 ∘ raw36315step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36315step0 raw36315step0Labels raw36315step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw36316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw36316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36316step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36316step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw36316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36316 raw36316Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw36316 raw36316Labels = mixedMoment B raw36316step0 raw36316step0Labels := by
      have ha : raw36316step0 = (fun i j => raw36316 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36316step0 raw36316; decide +kernel
      have hl : raw36316step0Labels = raw36316Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36316 raw36316Labels permutation162 permutation5
    mixedMoment B raw36316step0 raw36316step0Labels = mixedMoment B raw36316step1 raw36316step1Labels := by
      have ha : raw36316step1 = -raw36316step0 := by apply Matrix.ext; change ∀ i j, raw36316step1 i j = -(raw36316step0 i j); unfold raw36316step1 raw36316step0; decide +kernel
      have hl : raw36316step1Labels = raw36316step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36316step1 raw36316step1Labels = mixedMoment B raw36316step2 raw36316step2Labels := by
      have ha : raw36316step2 = raw36316step1 := by apply Matrix.ext; unfold raw36316step2 raw36316step1; decide +kernel
      have hl : raw36316step1Labels = labelEmbedding1 ∘ raw36316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36316step1 raw36316step1Labels raw36316step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw36317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36317step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36317step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36317step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36317 raw36317Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw36317 raw36317Labels = mixedMoment B raw36317step0 raw36317step0Labels := by
      have ha : raw36317step0 = (fun i j => raw36317 (permutation276 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36317step0 raw36317; decide +kernel
      have hl : raw36317step0Labels = raw36317Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36317 raw36317Labels permutation276 permutation5
    mixedMoment B raw36317step0 raw36317step0Labels = mixedMoment B raw36317step1 raw36317step1Labels := by
      have ha : raw36317step1 = -raw36317step0 := by apply Matrix.ext; change ∀ i j, raw36317step1 i j = -(raw36317step0 i j); unfold raw36317step1 raw36317step0; decide +kernel
      have hl : raw36317step1Labels = raw36317step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36317step1 raw36317step1Labels = mixedMoment B raw36317step2 raw36317step2Labels := by
      have ha : raw36317step2 = raw36317step1 := by apply Matrix.ext; unfold raw36317step2 raw36317step1; decide +kernel
      have hl : raw36317step1Labels = labelEmbedding1 ∘ raw36317step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36317step1 raw36317step1Labels raw36317step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

def raw36318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36318 raw36318Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw36318 raw36318Labels = mixedMoment B raw36318step0 raw36318step0Labels := by
      have ha : raw36318step0 = (fun i j => raw36318 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36318step0 raw36318; decide +kernel
      have hl : raw36318step0Labels = raw36318Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36318 raw36318Labels permutation663 permutation7
    mixedMoment B raw36318step0 raw36318step0Labels = mixedMoment B raw36318step1 raw36318step1Labels := by
      have ha : raw36318step1 = raw36318step0 := by apply Matrix.ext; unfold raw36318step1 raw36318step0; decide +kernel
      have hl : raw36318step0Labels = labelEmbedding1 ∘ raw36318step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36318step0 raw36318step0Labels raw36318step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

def raw36319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36319step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36319step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36319 raw36319Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw36319 raw36319Labels = mixedMoment B raw36319step0 raw36319step0Labels := by
      have hz : ∀ j, raw36319 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36319step0 = (fun i j => raw36319 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36319step0 raw36319; decide +kernel
      have hl : raw36319step0Labels = raw36319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36319 raw36319Labels permutation520 hz
    mixedMoment B raw36319step0 raw36319step0Labels = mixedMoment B raw36319step1 raw36319step1Labels := by
      have ha : raw36319step1 = (fun i j => raw36319step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36319step1 raw36319step0; decide +kernel
      have hl : raw36319step1Labels = raw36319step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36319step0 raw36319step0Labels permutation150 permutation7
    mixedMoment B raw36319step1 raw36319step1Labels = mixedMoment B raw36319step2 raw36319step2Labels := by
      have ha : raw36319step2 = raw36319step1 := by apply Matrix.ext; unfold raw36319step2 raw36319step1; decide +kernel
      have hl : raw36319step1Labels = labelEmbedding1 ∘ raw36319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36319step1 raw36319step1Labels raw36319step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

def raw36320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36320 raw36320Labels = mixedMoment B node3973 node3973Labels := by
  calc
    mixedMoment B raw36320 raw36320Labels = mixedMoment B raw36320step0 raw36320step0Labels := by
      have ha : raw36320step0 = (fun i j => raw36320 (permutation408 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36320step0 raw36320; decide +kernel
      have hl : raw36320step0Labels = raw36320Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36320 raw36320Labels permutation408 permutation5
    mixedMoment B raw36320step0 raw36320step0Labels = mixedMoment B raw36320step1 raw36320step1Labels := by
      have ha : raw36320step1 = raw36320step0 := by apply Matrix.ext; unfold raw36320step1 raw36320step0; decide +kernel
      have hl : raw36320step0Labels = labelEmbedding1 ∘ raw36320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36320step0 raw36320step0Labels raw36320step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3973 node3973Labels := by rfl

def raw36321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36321step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36321step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36321 raw36321Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw36321 raw36321Labels = mixedMoment B raw36321step0 raw36321step0Labels := by
      have ha : raw36321step0 = (fun i j => raw36321 (permutation284 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36321step0 raw36321; decide +kernel
      have hl : raw36321step0Labels = raw36321Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36321 raw36321Labels permutation284 permutation5
    mixedMoment B raw36321step0 raw36321step0Labels = mixedMoment B raw36321step1 raw36321step1Labels := by
      have ha : raw36321step1 = -raw36321step0 := by apply Matrix.ext; change ∀ i j, raw36321step1 i j = -(raw36321step0 i j); unfold raw36321step1 raw36321step0; decide +kernel
      have hl : raw36321step1Labels = raw36321step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36321step1 raw36321step1Labels = mixedMoment B raw36321step2 raw36321step2Labels := by
      have ha : raw36321step2 = raw36321step1 := by apply Matrix.ext; unfold raw36321step2 raw36321step1; decide +kernel
      have hl : raw36321step1Labels = labelEmbedding1 ∘ raw36321step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36321step1 raw36321step1Labels raw36321step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

def raw36322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36322 raw36322Labels = mixedMoment B node3756 node3756Labels := by
  calc
    mixedMoment B raw36322 raw36322Labels = mixedMoment B raw36322step0 raw36322step0Labels := by
      have ha : raw36322step0 = (fun i j => raw36322 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36322step0 raw36322; decide +kernel
      have hl : raw36322step0Labels = raw36322Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36322 raw36322Labels permutation663 permutation7
    mixedMoment B raw36322step0 raw36322step0Labels = mixedMoment B raw36322step1 raw36322step1Labels := by
      have ha : raw36322step1 = raw36322step0 := by apply Matrix.ext; unfold raw36322step1 raw36322step0; decide +kernel
      have hl : raw36322step0Labels = labelEmbedding1 ∘ raw36322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36322step0 raw36322step0Labels raw36322step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3756 node3756Labels := by rfl

def raw36323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36323step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36323step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36323 raw36323Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw36323 raw36323Labels = mixedMoment B raw36323step0 raw36323step0Labels := by
      have hz : ∀ j, raw36323 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36323step0 = (fun i j => raw36323 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36323step0 raw36323; decide +kernel
      have hl : raw36323step0Labels = raw36323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36323 raw36323Labels permutation520 hz
    mixedMoment B raw36323step0 raw36323step0Labels = mixedMoment B raw36323step1 raw36323step1Labels := by
      have ha : raw36323step1 = (fun i j => raw36323step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36323step1 raw36323step0; decide +kernel
      have hl : raw36323step1Labels = raw36323step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36323step0 raw36323step0Labels permutation150 permutation7
    mixedMoment B raw36323step1 raw36323step1Labels = mixedMoment B raw36323step2 raw36323step2Labels := by
      have ha : raw36323step2 = raw36323step1 := by apply Matrix.ext; unfold raw36323step2 raw36323step1; decide +kernel
      have hl : raw36323step1Labels = labelEmbedding1 ∘ raw36323step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36323step1 raw36323step1Labels raw36323step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

def raw36324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36324step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36324 raw36324Labels = mixedMoment B node3951 node3951Labels := by
  calc
    mixedMoment B raw36324 raw36324Labels = mixedMoment B raw36324step0 raw36324step0Labels := by
      have ha : raw36324step0 = (fun i j => raw36324 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36324step0 raw36324; decide +kernel
      have hl : raw36324step0Labels = raw36324Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36324 raw36324Labels permutation663 permutation7
    mixedMoment B raw36324step0 raw36324step0Labels = mixedMoment B raw36324step1 raw36324step1Labels := by
      have ha : raw36324step1 = raw36324step0 := by apply Matrix.ext; unfold raw36324step1 raw36324step0; decide +kernel
      have hl : raw36324step0Labels = labelEmbedding1 ∘ raw36324step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36324step0 raw36324step0Labels raw36324step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3951 node3951Labels := by rfl

def raw36325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw36325step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36325step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36325step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw36325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36325 raw36325Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw36325 raw36325Labels = mixedMoment B raw36325step0 raw36325step0Labels := by
      have ha : raw36325step0 = (fun i j => raw36325 (permutation275 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36325step0 raw36325; decide +kernel
      have hl : raw36325step0Labels = raw36325Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36325 raw36325Labels permutation275 permutation5
    mixedMoment B raw36325step0 raw36325step0Labels = mixedMoment B raw36325step1 raw36325step1Labels := by
      have ha : raw36325step1 = -raw36325step0 := by apply Matrix.ext; change ∀ i j, raw36325step1 i j = -(raw36325step0 i j); unfold raw36325step1 raw36325step0; decide +kernel
      have hl : raw36325step1Labels = raw36325step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36325step1 raw36325step1Labels = mixedMoment B raw36325step2 raw36325step2Labels := by
      have ha : raw36325step2 = raw36325step1 := by apply Matrix.ext; unfold raw36325step2 raw36325step1; decide +kernel
      have hl : raw36325step1Labels = labelEmbedding1 ∘ raw36325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36325step1 raw36325step1Labels raw36325step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

def raw36326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36326step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36326step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36326 raw36326Labels = mixedMoment B node3792 node3792Labels := by
  calc
    mixedMoment B raw36326 raw36326Labels = mixedMoment B raw36326step0 raw36326step0Labels := by
      have ha : raw36326step0 = (fun i j => raw36326 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36326step0 raw36326; decide +kernel
      have hl : raw36326step0Labels = raw36326Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36326 raw36326Labels permutation663 permutation7
    mixedMoment B raw36326step0 raw36326step0Labels = mixedMoment B raw36326step1 raw36326step1Labels := by
      have ha : raw36326step1 = raw36326step0 := by apply Matrix.ext; unfold raw36326step1 raw36326step0; decide +kernel
      have hl : raw36326step0Labels = labelEmbedding1 ∘ raw36326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36326step0 raw36326step0Labels raw36326step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3792 node3792Labels := by rfl

def raw36327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36327step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36327 raw36327Labels = mixedMoment B node3835 node3835Labels := by
  calc
    mixedMoment B raw36327 raw36327Labels = mixedMoment B raw36327step0 raw36327step0Labels := by
      have ha : raw36327step0 = (fun i j => raw36327 (permutation551 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36327step0 raw36327; decide +kernel
      have hl : raw36327step0Labels = raw36327Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36327 raw36327Labels permutation551 permutation5
    mixedMoment B raw36327step0 raw36327step0Labels = mixedMoment B raw36327step1 raw36327step1Labels := by
      have ha : raw36327step1 = raw36327step0 := by apply Matrix.ext; unfold raw36327step1 raw36327step0; decide +kernel
      have hl : raw36327step0Labels = labelEmbedding1 ∘ raw36327step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36327step0 raw36327step0Labels raw36327step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3835 node3835Labels := by rfl

def raw36328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36328 raw36328Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw36328 raw36328Labels = mixedMoment B raw36328step0 raw36328step0Labels := by
      have ha : raw36328step0 = (fun i j => raw36328 (permutation545 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36328step0 raw36328; decide +kernel
      have hl : raw36328step0Labels = raw36328Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36328 raw36328Labels permutation545 permutation5
    mixedMoment B raw36328step0 raw36328step0Labels = mixedMoment B raw36328step1 raw36328step1Labels := by
      have ha : raw36328step1 = raw36328step0 := by apply Matrix.ext; unfold raw36328step1 raw36328step0; decide +kernel
      have hl : raw36328step0Labels = labelEmbedding1 ∘ raw36328step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36328step0 raw36328step0Labels raw36328step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

def raw36329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw36329step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36329step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36329step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw36329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36329 raw36329Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw36329 raw36329Labels = mixedMoment B raw36329step0 raw36329step0Labels := by
      have ha : raw36329step0 = (fun i j => raw36329 (permutation271 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36329step0 raw36329; decide +kernel
      have hl : raw36329step0Labels = raw36329Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36329 raw36329Labels permutation271 permutation5
    mixedMoment B raw36329step0 raw36329step0Labels = mixedMoment B raw36329step1 raw36329step1Labels := by
      have ha : raw36329step1 = -raw36329step0 := by apply Matrix.ext; change ∀ i j, raw36329step1 i j = -(raw36329step0 i j); unfold raw36329step1 raw36329step0; decide +kernel
      have hl : raw36329step1Labels = raw36329step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36329step1 raw36329step1Labels = mixedMoment B raw36329step2 raw36329step2Labels := by
      have ha : raw36329step2 = raw36329step1 := by apply Matrix.ext; unfold raw36329step2 raw36329step1; decide +kernel
      have hl : raw36329step1Labels = labelEmbedding1 ∘ raw36329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36329step1 raw36329step1Labels raw36329step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

def raw36330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36330step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36330 raw36330Labels = mixedMoment B node3456 node3456Labels := by
  calc
    mixedMoment B raw36330 raw36330Labels = mixedMoment B raw36330step0 raw36330step0Labels := by
      have ha : raw36330step0 = (fun i j => raw36330 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36330step0 raw36330; decide +kernel
      have hl : raw36330step0Labels = raw36330Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36330 raw36330Labels permutation663 permutation7
    mixedMoment B raw36330step0 raw36330step0Labels = mixedMoment B raw36330step1 raw36330step1Labels := by
      have ha : raw36330step1 = raw36330step0 := by apply Matrix.ext; unfold raw36330step1 raw36330step0; decide +kernel
      have hl : raw36330step0Labels = labelEmbedding1 ∘ raw36330step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36330step0 raw36330step0Labels raw36330step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3456 node3456Labels := by rfl

def raw36331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36331step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36331 raw36331Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw36331 raw36331Labels = mixedMoment B raw36331step0 raw36331step0Labels := by
      have ha : raw36331step0 = (fun i j => raw36331 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36331step0 raw36331; decide +kernel
      have hl : raw36331step0Labels = raw36331Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36331 raw36331Labels permutation663 permutation7
    mixedMoment B raw36331step0 raw36331step0Labels = mixedMoment B raw36331step1 raw36331step1Labels := by
      have ha : raw36331step1 = raw36331step0 := by apply Matrix.ext; unfold raw36331step1 raw36331step0; decide +kernel
      have hl : raw36331step0Labels = labelEmbedding1 ∘ raw36331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36331step0 raw36331step0Labels raw36331step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3520 node3520Labels := by rfl

def raw36332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw36332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw36332step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36332step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36332 raw36332Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw36332 raw36332Labels = mixedMoment B raw36332step0 raw36332step0Labels := by
      have hz : ∀ j, raw36332 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36332step0 = (fun i j => raw36332 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36332step0 raw36332; decide +kernel
      have hl : raw36332step0Labels = raw36332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36332 raw36332Labels permutation520 hz
    mixedMoment B raw36332step0 raw36332step0Labels = mixedMoment B raw36332step1 raw36332step1Labels := by
      have ha : raw36332step1 = (fun i j => raw36332step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36332step1 raw36332step0; decide +kernel
      have hl : raw36332step1Labels = raw36332step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36332step0 raw36332step0Labels permutation150 permutation7
    mixedMoment B raw36332step1 raw36332step1Labels = mixedMoment B raw36332step2 raw36332step2Labels := by
      have ha : raw36332step2 = raw36332step1 := by apply Matrix.ext; unfold raw36332step2 raw36332step1; decide +kernel
      have hl : raw36332step1Labels = labelEmbedding1 ∘ raw36332step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36332step1 raw36332step1Labels raw36332step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

def raw36333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36333step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36333 raw36333Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw36333 raw36333Labels = mixedMoment B raw36333step0 raw36333step0Labels := by
      have ha : raw36333step0 = (fun i j => raw36333 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36333step0 raw36333; decide +kernel
      have hl : raw36333step0Labels = raw36333Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36333 raw36333Labels permutation267 permutation3
    mixedMoment B raw36333step0 raw36333step0Labels = mixedMoment B raw36333step1 raw36333step1Labels := by
      have ha : raw36333step1 = raw36333step0 := by apply Matrix.ext; unfold raw36333step1 raw36333step0; decide +kernel
      have hl : raw36333step0Labels = labelEmbedding6 ∘ raw36333step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36333step0 raw36333step0Labels raw36333step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw36334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw36334step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36334step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36334step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36334step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36334 raw36334Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw36334 raw36334Labels = mixedMoment B raw36334step0 raw36334step0Labels := by
      have ha : raw36334step0 = (fun i j => raw36334 (permutation660 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36334step0 raw36334; decide +kernel
      have hl : raw36334step0Labels = raw36334Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36334 raw36334Labels permutation660 permutation3
    mixedMoment B raw36334step0 raw36334step0Labels = mixedMoment B raw36334step1 raw36334step1Labels := by
      have ha : raw36334step1 = -raw36334step0 := by apply Matrix.ext; change ∀ i j, raw36334step1 i j = -(raw36334step0 i j); unfold raw36334step1 raw36334step0; decide +kernel
      have hl : raw36334step1Labels = raw36334step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36334step1 raw36334step1Labels = mixedMoment B raw36334step2 raw36334step2Labels := by
      have ha : raw36334step2 = raw36334step1 := by apply Matrix.ext; unfold raw36334step2 raw36334step1; decide +kernel
      have hl : raw36334step1Labels = labelEmbedding6 ∘ raw36334step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36334step1 raw36334step1Labels raw36334step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw36335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36335step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36335step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36335step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36335step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36335 raw36335Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw36335 raw36335Labels = mixedMoment B raw36335step0 raw36335step0Labels := by
      have hz : ∀ j, raw36335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36335step0 = (fun i j => raw36335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36335step0 raw36335; decide +kernel
      have hl : raw36335step0Labels = raw36335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36335 raw36335Labels permutation434 hz
    mixedMoment B raw36335step0 raw36335step0Labels = mixedMoment B raw36335step1 raw36335step1Labels := by
      have ha : raw36335step1 = (fun i j => raw36335step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36335step1 raw36335step0; decide +kernel
      have hl : raw36335step1Labels = raw36335step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36335step0 raw36335step0Labels permutation150 permutation3
    mixedMoment B raw36335step1 raw36335step1Labels = mixedMoment B raw36335step2 raw36335step2Labels := by
      have ha : raw36335step2 = -raw36335step1 := by apply Matrix.ext; change ∀ i j, raw36335step2 i j = -(raw36335step1 i j); unfold raw36335step2 raw36335step1; decide +kernel
      have hl : raw36335step2Labels = raw36335step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36335step2 raw36335step2Labels = mixedMoment B raw36335step3 raw36335step3Labels := by
      have ha : raw36335step3 = raw36335step2 := by apply Matrix.ext; unfold raw36335step3 raw36335step2; decide +kernel
      have hl : raw36335step2Labels = labelEmbedding6 ∘ raw36335step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36335step2 raw36335step2Labels raw36335step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw36336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw36336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36336step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36336step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36336step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36336step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36336step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36336 raw36336Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw36336 raw36336Labels = mixedMoment B raw36336step0 raw36336step0Labels := by
      have ha : raw36336step0 = (fun i j => raw36336 (permutation657 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36336step0 raw36336; decide +kernel
      have hl : raw36336step0Labels = raw36336Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36336 raw36336Labels permutation657 permutation3
    mixedMoment B raw36336step0 raw36336step0Labels = mixedMoment B raw36336step1 raw36336step1Labels := by
      have ha : raw36336step1 = -raw36336step0 := by apply Matrix.ext; change ∀ i j, raw36336step1 i j = -(raw36336step0 i j); unfold raw36336step1 raw36336step0; decide +kernel
      have hl : raw36336step1Labels = raw36336step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36336step1 raw36336step1Labels = mixedMoment B raw36336step2 raw36336step2Labels := by
      have ha : raw36336step2 = raw36336step1 := by apply Matrix.ext; unfold raw36336step2 raw36336step1; decide +kernel
      have hl : raw36336step1Labels = labelEmbedding6 ∘ raw36336step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36336step1 raw36336step1Labels raw36336step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw36337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw36337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36337 raw36337Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw36337 raw36337Labels = mixedMoment B raw36337step0 raw36337step0Labels := by
      have ha : raw36337step0 = (fun i j => raw36337 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36337step0 raw36337; decide +kernel
      have hl : raw36337step0Labels = raw36337Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36337 raw36337Labels permutation266 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw36338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36338step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36338 raw36338Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw36338 raw36338Labels = mixedMoment B raw36338step0 raw36338step0Labels := by
      have ha : raw36338step0 = (fun i j => raw36338 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36338step0 raw36338; decide +kernel
      have hl : raw36338step0Labels = raw36338Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36338 raw36338Labels permutation154 permutation3
    mixedMoment B raw36338step0 raw36338step0Labels = mixedMoment B raw36338step1 raw36338step1Labels := by
      have ha : raw36338step1 = raw36338step0 := by apply Matrix.ext; unfold raw36338step1 raw36338step0; decide +kernel
      have hl : raw36338step0Labels = labelEmbedding6 ∘ raw36338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36338step0 raw36338step0Labels raw36338step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw36339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36339step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36339step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36339step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36339 raw36339Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw36339 raw36339Labels = mixedMoment B raw36339step0 raw36339step0Labels := by
      have ha : raw36339step0 = (fun i j => raw36339 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36339step0 raw36339; decide +kernel
      have hl : raw36339step0Labels = raw36339Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36339 raw36339Labels permutation267 permutation3
    mixedMoment B raw36339step0 raw36339step0Labels = mixedMoment B raw36339step1 raw36339step1Labels := by
      have ha : raw36339step1 = raw36339step0 := by apply Matrix.ext; unfold raw36339step1 raw36339step0; decide +kernel
      have hl : raw36339step0Labels = labelEmbedding6 ∘ raw36339step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36339step0 raw36339step0Labels raw36339step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw36340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36340step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36340step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36340step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36340step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36340 raw36340Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw36340 raw36340Labels = mixedMoment B raw36340step0 raw36340step0Labels := by
      have hz : ∀ j, raw36340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36340step0 = (fun i j => raw36340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36340step0 raw36340; decide +kernel
      have hl : raw36340step0Labels = raw36340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36340 raw36340Labels permutation434 hz
    mixedMoment B raw36340step0 raw36340step0Labels = mixedMoment B raw36340step1 raw36340step1Labels := by
      have ha : raw36340step1 = (fun i j => raw36340step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36340step1 raw36340step0; decide +kernel
      have hl : raw36340step1Labels = raw36340step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36340step0 raw36340step0Labels permutation144 permutation3
    mixedMoment B raw36340step1 raw36340step1Labels = mixedMoment B raw36340step2 raw36340step2Labels := by
      have ha : raw36340step2 = -raw36340step1 := by apply Matrix.ext; change ∀ i j, raw36340step2 i j = -(raw36340step1 i j); unfold raw36340step2 raw36340step1; decide +kernel
      have hl : raw36340step2Labels = raw36340step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36340step2 raw36340step2Labels = mixedMoment B raw36340step3 raw36340step3Labels := by
      have ha : raw36340step3 = raw36340step2 := by apply Matrix.ext; unfold raw36340step3 raw36340step2; decide +kernel
      have hl : raw36340step2Labels = labelEmbedding6 ∘ raw36340step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36340step2 raw36340step2Labels raw36340step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw36341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw36341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36341step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36341step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36341step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36341 raw36341Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw36341 raw36341Labels = mixedMoment B raw36341step0 raw36341step0Labels := by
      have ha : raw36341step0 = (fun i j => raw36341 (permutation657 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36341step0 raw36341; decide +kernel
      have hl : raw36341step0Labels = raw36341Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36341 raw36341Labels permutation657 permutation3
    mixedMoment B raw36341step0 raw36341step0Labels = mixedMoment B raw36341step1 raw36341step1Labels := by
      have ha : raw36341step1 = -raw36341step0 := by apply Matrix.ext; change ∀ i j, raw36341step1 i j = -(raw36341step0 i j); unfold raw36341step1 raw36341step0; decide +kernel
      have hl : raw36341step1Labels = raw36341step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36341step1 raw36341step1Labels = mixedMoment B raw36341step2 raw36341step2Labels := by
      have ha : raw36341step2 = raw36341step1 := by apply Matrix.ext; unfold raw36341step2 raw36341step1; decide +kernel
      have hl : raw36341step1Labels = labelEmbedding6 ∘ raw36341step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36341step1 raw36341step1Labels raw36341step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw36342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw36342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36342 raw36342Labels = mixedMoment B node5464 node5464Labels := by
  calc
    mixedMoment B raw36342 raw36342Labels = mixedMoment B raw36342step0 raw36342step0Labels := by
      have ha : raw36342step0 = (fun i j => raw36342 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36342step0 raw36342; decide +kernel
      have hl : raw36342step0Labels = raw36342Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36342 raw36342Labels permutation162 permutation2
    _ = mixedMoment B node5464 node5464Labels := by rfl

def raw36343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw36343step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36343step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw36343step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36343 raw36343Labels = mixedMoment B node4926 node4926Labels := by
  calc
    mixedMoment B raw36343 raw36343Labels = mixedMoment B raw36343step0 raw36343step0Labels := by
      have ha : raw36343step0 = (fun i j => raw36343 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36343step0 raw36343; decide +kernel
      have hl : raw36343step0Labels = raw36343Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36343 raw36343Labels permutation267 permutation3
    mixedMoment B raw36343step0 raw36343step0Labels = mixedMoment B raw36343step1 raw36343step1Labels := by
      have ha : raw36343step1 = raw36343step0 := by apply Matrix.ext; unfold raw36343step1 raw36343step0; decide +kernel
      have hl : raw36343step0Labels = labelEmbedding6 ∘ raw36343step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36343step0 raw36343step0Labels raw36343step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4926 node4926Labels := by rfl

def raw36344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36344step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36344step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36344step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36344step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36344step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36344 raw36344Labels = mixedMoment B node5316 node5316Labels := by
  calc
    mixedMoment B raw36344 raw36344Labels = mixedMoment B raw36344step0 raw36344step0Labels := by
      have ha : raw36344step0 = (fun i j => raw36344 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36344step0 raw36344; decide +kernel
      have hl : raw36344step0Labels = raw36344Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36344 raw36344Labels permutation518 permutation3
    mixedMoment B raw36344step0 raw36344step0Labels = mixedMoment B raw36344step1 raw36344step1Labels := by
      have ha : raw36344step1 = -raw36344step0 := by apply Matrix.ext; change ∀ i j, raw36344step1 i j = -(raw36344step0 i j); unfold raw36344step1 raw36344step0; decide +kernel
      have hl : raw36344step1Labels = raw36344step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36344step1 raw36344step1Labels = mixedMoment B raw36344step2 raw36344step2Labels := by
      have ha : raw36344step2 = raw36344step1 := by apply Matrix.ext; unfold raw36344step2 raw36344step1; decide +kernel
      have hl : raw36344step1Labels = labelEmbedding6 ∘ raw36344step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36344step1 raw36344step1Labels raw36344step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5316 node5316Labels := by rfl

def raw36345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw36345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36345step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36345step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36345step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36345step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36345step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36345 raw36345Labels = mixedMoment B node5321 node5321Labels := by
  calc
    mixedMoment B raw36345 raw36345Labels = mixedMoment B raw36345step0 raw36345step0Labels := by
      have ha : raw36345step0 = (fun i j => raw36345 (permutation512 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36345step0 raw36345; decide +kernel
      have hl : raw36345step0Labels = raw36345Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36345 raw36345Labels permutation512 permutation3
    mixedMoment B raw36345step0 raw36345step0Labels = mixedMoment B raw36345step1 raw36345step1Labels := by
      have ha : raw36345step1 = -raw36345step0 := by apply Matrix.ext; change ∀ i j, raw36345step1 i j = -(raw36345step0 i j); unfold raw36345step1 raw36345step0; decide +kernel
      have hl : raw36345step1Labels = raw36345step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36345step1 raw36345step1Labels = mixedMoment B raw36345step2 raw36345step2Labels := by
      have ha : raw36345step2 = raw36345step1 := by apply Matrix.ext; unfold raw36345step2 raw36345step1; decide +kernel
      have hl : raw36345step1Labels = labelEmbedding6 ∘ raw36345step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36345step1 raw36345step1Labels raw36345step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5321 node5321Labels := by rfl

def raw36346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw36346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36346step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36346step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36346step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36346step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36346 raw36346Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw36346 raw36346Labels = mixedMoment B raw36346step0 raw36346step0Labels := by
      have ha : raw36346step0 = (fun i j => raw36346 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36346step0 raw36346; decide +kernel
      have hl : raw36346step0Labels = raw36346Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36346 raw36346Labels permutation518 permutation3
    mixedMoment B raw36346step0 raw36346step0Labels = mixedMoment B raw36346step1 raw36346step1Labels := by
      have ha : raw36346step1 = -raw36346step0 := by apply Matrix.ext; change ∀ i j, raw36346step1 i j = -(raw36346step0 i j); unfold raw36346step1 raw36346step0; decide +kernel
      have hl : raw36346step1Labels = raw36346step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36346step1 raw36346step1Labels = mixedMoment B raw36346step2 raw36346step2Labels := by
      have ha : raw36346step2 = raw36346step1 := by apply Matrix.ext; unfold raw36346step2 raw36346step1; decide +kernel
      have hl : raw36346step1Labels = labelEmbedding6 ∘ raw36346step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36346step1 raw36346step1Labels raw36346step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw36347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw36347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36347step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36347step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36347step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36347 raw36347Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw36347 raw36347Labels = mixedMoment B raw36347step0 raw36347step0Labels := by
      have ha : raw36347step0 = (fun i j => raw36347 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36347step0 raw36347; decide +kernel
      have hl : raw36347step0Labels = raw36347Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36347 raw36347Labels permutation265 permutation3
    mixedMoment B raw36347step0 raw36347step0Labels = mixedMoment B raw36347step1 raw36347step1Labels := by
      have ha : raw36347step1 = raw36347step0 := by apply Matrix.ext; unfold raw36347step1 raw36347step0; decide +kernel
      have hl : raw36347step0Labels = labelEmbedding6 ∘ raw36347step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36347step0 raw36347step0Labels raw36347step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

def raw36348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw36348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36348step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36348step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36348step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36348step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36348 raw36348Labels = mixedMoment B node5334 node5334Labels := by
  calc
    mixedMoment B raw36348 raw36348Labels = mixedMoment B raw36348step0 raw36348step0Labels := by
      have ha : raw36348step0 = (fun i j => raw36348 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36348step0 raw36348; decide +kernel
      have hl : raw36348step0Labels = raw36348Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36348 raw36348Labels permutation687 permutation3
    mixedMoment B raw36348step0 raw36348step0Labels = mixedMoment B raw36348step1 raw36348step1Labels := by
      have ha : raw36348step1 = -raw36348step0 := by apply Matrix.ext; change ∀ i j, raw36348step1 i j = -(raw36348step0 i j); unfold raw36348step1 raw36348step0; decide +kernel
      have hl : raw36348step1Labels = raw36348step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36348step1 raw36348step1Labels = mixedMoment B raw36348step2 raw36348step2Labels := by
      have ha : raw36348step2 = raw36348step1 := by apply Matrix.ext; unfold raw36348step2 raw36348step1; decide +kernel
      have hl : raw36348step1Labels = labelEmbedding6 ∘ raw36348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36348step1 raw36348step1Labels raw36348step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5334 node5334Labels := by rfl

def raw36349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw36349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36349step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36349step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36349step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36349step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36349 raw36349Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36349 raw36349Labels = mixedMoment B raw36349step0 raw36349step0Labels := by
      have hz : ∀ j, raw36349 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36349step0 = (fun i j => raw36349 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36349step0 raw36349; decide +kernel
      have hl : raw36349step0Labels = raw36349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36349 raw36349Labels permutation434 hz
    mixedMoment B raw36349step0 raw36349step0Labels = mixedMoment B raw36349step1 raw36349step1Labels := by
      have ha : raw36349step1 = (fun i j => raw36349step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36349step1 raw36349step0; decide +kernel
      have hl : raw36349step1Labels = raw36349step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36349step0 raw36349step0Labels permutation150 permutation3
    mixedMoment B raw36349step1 raw36349step1Labels = mixedMoment B raw36349step2 raw36349step2Labels := by
      have ha : raw36349step2 = -raw36349step1 := by apply Matrix.ext; change ∀ i j, raw36349step2 i j = -(raw36349step1 i j); unfold raw36349step2 raw36349step1; decide +kernel
      have hl : raw36349step2Labels = raw36349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36349step2 raw36349step2Labels = mixedMoment B raw36349step3 raw36349step3Labels := by
      have ha : raw36349step3 = raw36349step2 := by apply Matrix.ext; unfold raw36349step3 raw36349step2; decide +kernel
      have hl : raw36349step2Labels = labelEmbedding6 ∘ raw36349step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36349step2 raw36349step2Labels raw36349step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw36350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw36350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36350step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36350step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36350 raw36350Labels = mixedMoment B node5460 node5460Labels := by
  calc
    mixedMoment B raw36350 raw36350Labels = mixedMoment B raw36350step0 raw36350step0Labels := by
      have ha : raw36350step0 = (fun i j => raw36350 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36350step0 raw36350; decide +kernel
      have hl : raw36350step0Labels = raw36350Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36350 raw36350Labels permutation153 permutation3
    mixedMoment B raw36350step0 raw36350step0Labels = mixedMoment B raw36350step1 raw36350step1Labels := by
      have ha : raw36350step1 = raw36350step0 := by apply Matrix.ext; unfold raw36350step1 raw36350step0; decide +kernel
      have hl : raw36350step0Labels = labelEmbedding6 ∘ raw36350step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36350step0 raw36350step0Labels raw36350step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5460 node5460Labels := by rfl

def raw36351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw36351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw36351step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw36351step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36351step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw36351step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36351 raw36351Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw36351 raw36351Labels = mixedMoment B raw36351step0 raw36351step0Labels := by
      have ha : raw36351step0 = (fun i j => raw36351 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36351step0 raw36351; decide +kernel
      have hl : raw36351step0Labels = raw36351Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36351 raw36351Labels permutation663 permutation3
    mixedMoment B raw36351step0 raw36351step0Labels = mixedMoment B raw36351step1 raw36351step1Labels := by
      have ha : raw36351step1 = -raw36351step0 := by apply Matrix.ext; change ∀ i j, raw36351step1 i j = -(raw36351step0 i j); unfold raw36351step1 raw36351step0; decide +kernel
      have hl : raw36351step1Labels = raw36351step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36351step1 raw36351step1Labels = mixedMoment B raw36351step2 raw36351step2Labels := by
      have ha : raw36351step2 = raw36351step1 := by apply Matrix.ext; unfold raw36351step2 raw36351step1; decide +kernel
      have hl : raw36351step1Labels = labelEmbedding6 ∘ raw36351step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36351step1 raw36351step1Labels raw36351step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4706 node4706Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
