import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14976 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -2, 1], ![-3, 1, 2]]
def raw14976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14976step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14976 raw14976Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw14976 raw14976Labels = mixedMoment B raw14976step0 raw14976step0Labels := by
      have hz : ∀ j, raw14976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14976step0 = (fun i j => raw14976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14976step0 raw14976; decide +kernel
      have hl : raw14976step0Labels = raw14976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14976 raw14976Labels permutation434 hz
    mixedMoment B raw14976step0 raw14976step0Labels = mixedMoment B raw14976step1 raw14976step1Labels := by
      have hz : ∀ j, raw14976step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14976step1 = (fun i j => raw14976step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14976step1 raw14976step0; decide +kernel
      have hl : raw14976step1Labels = raw14976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14976step0 raw14976step0Labels permutation80 hz
    mixedMoment B raw14976step1 raw14976step1Labels = mixedMoment B raw14976step2 raw14976step2Labels := by
      have ha : raw14976step2 = (fun i j => raw14976step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14976step2 raw14976step1; decide +kernel
      have hl : raw14976step2Labels = raw14976step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14976step1 raw14976step1Labels permutation31 permutation2
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw14977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw14977step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14977step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14977step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14977step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14977 raw14977Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw14977 raw14977Labels = mixedMoment B raw14977step0 raw14977step0Labels := by
      have hz : ∀ j, raw14977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14977step0 = (fun i j => raw14977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14977step0 raw14977; decide +kernel
      have hl : raw14977step0Labels = raw14977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14977 raw14977Labels permutation434 hz
    mixedMoment B raw14977step0 raw14977step0Labels = mixedMoment B raw14977step1 raw14977step1Labels := by
      have hz : ∀ j, raw14977step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14977step1 = (fun i j => raw14977step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14977step1 raw14977step0; decide +kernel
      have hl : raw14977step1Labels = raw14977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14977step0 raw14977step0Labels permutation80 hz
    mixedMoment B raw14977step1 raw14977step1Labels = mixedMoment B raw14977step2 raw14977step2Labels := by
      have ha : raw14977step2 = (fun i j => raw14977step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14977step2 raw14977step1; decide +kernel
      have hl : raw14977step2Labels = raw14977step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14977step1 raw14977step1Labels permutation12 permutation4
    mixedMoment B raw14977step2 raw14977step2Labels = mixedMoment B raw14977step3 raw14977step3Labels := by
      have ha : raw14977step3 = -raw14977step2 := by apply Matrix.ext; change ∀ i j, raw14977step3 i j = -(raw14977step2 i j); unfold raw14977step3 raw14977step2; decide +kernel
      have hl : raw14977step3Labels = raw14977step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14977step3 raw14977step3Labels = mixedMoment B raw14977step4 raw14977step4Labels := by
      have ha : raw14977step4 = raw14977step3 := by apply Matrix.ext; unfold raw14977step4 raw14977step3; decide +kernel
      have hl : raw14977step3Labels = labelEmbedding7 ∘ raw14977step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14977step3 raw14977step3Labels raw14977step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw14978 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14978 raw14978Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw14978 raw14978Labels = mixedMoment B raw14978step0 raw14978step0Labels := by
      have hz : ∀ j, raw14978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14978step0 = (fun i j => raw14978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14978step0 raw14978; decide +kernel
      have hl : raw14978step0Labels = raw14978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14978 raw14978Labels permutation346 hz
    mixedMoment B raw14978step0 raw14978step0Labels = mixedMoment B raw14978step1 raw14978step1Labels := by
      have ha : raw14978step1 = (fun i j => raw14978step0 (permutation141 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14978step1 raw14978step0; decide +kernel
      have hl : raw14978step1Labels = raw14978step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14978step0 raw14978step0Labels permutation141 permutation2
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw14979 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2]]
def raw14979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14979step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14979step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14979step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14979step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14979 raw14979Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw14979 raw14979Labels = mixedMoment B raw14979step0 raw14979step0Labels := by
      have hz : ∀ j, raw14979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14979step0 = (fun i j => raw14979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14979step0 raw14979; decide +kernel
      have hl : raw14979step0Labels = raw14979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14979 raw14979Labels permutation434 hz
    mixedMoment B raw14979step0 raw14979step0Labels = mixedMoment B raw14979step1 raw14979step1Labels := by
      have hz : ∀ j, raw14979step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14979step1 = (fun i j => raw14979step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14979step1 raw14979step0; decide +kernel
      have hl : raw14979step1Labels = raw14979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14979step0 raw14979step0Labels permutation80 hz
    mixedMoment B raw14979step1 raw14979step1Labels = mixedMoment B raw14979step2 raw14979step2Labels := by
      have ha : raw14979step2 = (fun i j => raw14979step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14979step2 raw14979step1; decide +kernel
      have hl : raw14979step2Labels = raw14979step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14979step1 raw14979step1Labels permutation31 permutation7
    mixedMoment B raw14979step2 raw14979step2Labels = mixedMoment B raw14979step3 raw14979step3Labels := by
      have ha : raw14979step3 = -raw14979step2 := by apply Matrix.ext; change ∀ i j, raw14979step3 i j = -(raw14979step2 i j); unfold raw14979step3 raw14979step2; decide +kernel
      have hl : raw14979step3Labels = raw14979step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14979step3 raw14979step3Labels = mixedMoment B raw14979step4 raw14979step4Labels := by
      have ha : raw14979step4 = raw14979step3 := by apply Matrix.ext; unfold raw14979step4 raw14979step3; decide +kernel
      have hl : raw14979step3Labels = labelEmbedding10 ∘ raw14979step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14979step3 raw14979step3Labels raw14979step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw14980 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -2, 1], ![-3, 1, 2]]
def raw14980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14980step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14980 raw14980Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw14980 raw14980Labels = mixedMoment B raw14980step0 raw14980step0Labels := by
      have hz : ∀ j, raw14980 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14980step0 = (fun i j => raw14980 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14980step0 raw14980; decide +kernel
      have hl : raw14980step0Labels = raw14980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14980 raw14980Labels permutation434 hz
    mixedMoment B raw14980step0 raw14980step0Labels = mixedMoment B raw14980step1 raw14980step1Labels := by
      have hz : ∀ j, raw14980step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14980step1 = (fun i j => raw14980step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14980step1 raw14980step0; decide +kernel
      have hl : raw14980step1Labels = raw14980step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14980step0 raw14980step0Labels permutation80 hz
    mixedMoment B raw14980step1 raw14980step1Labels = mixedMoment B raw14980step2 raw14980step2Labels := by
      have ha : raw14980step2 = (fun i j => raw14980step1 (permutation27 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14980step2 raw14980step1; decide +kernel
      have hl : raw14980step2Labels = raw14980step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14980step1 raw14980step1Labels permutation27 permutation2
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw14981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14981step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14981step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14981step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14981step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14981 raw14981Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw14981 raw14981Labels = mixedMoment B raw14981step0 raw14981step0Labels := by
      have hz : ∀ j, raw14981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14981step0 = (fun i j => raw14981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14981step0 raw14981; decide +kernel
      have hl : raw14981step0Labels = raw14981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14981 raw14981Labels permutation434 hz
    mixedMoment B raw14981step0 raw14981step0Labels = mixedMoment B raw14981step1 raw14981step1Labels := by
      have ha : raw14981step1 = (fun i j => raw14981step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14981step1 raw14981step0; decide +kernel
      have hl : raw14981step1Labels = raw14981step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14981step0 raw14981step0Labels permutation36 permutation4
    mixedMoment B raw14981step1 raw14981step1Labels = mixedMoment B raw14981step2 raw14981step2Labels := by
      have ha : raw14981step2 = -raw14981step1 := by apply Matrix.ext; change ∀ i j, raw14981step2 i j = -(raw14981step1 i j); unfold raw14981step2 raw14981step1; decide +kernel
      have hl : raw14981step2Labels = raw14981step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14981step2 raw14981step2Labels = mixedMoment B raw14981step3 raw14981step3Labels := by
      have ha : raw14981step3 = raw14981step2 := by apply Matrix.ext; unfold raw14981step3 raw14981step2; decide +kernel
      have hl : raw14981step2Labels = labelEmbedding7 ∘ raw14981step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14981step2 raw14981step2Labels raw14981step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw14982 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14982step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14982step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14982 raw14982Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw14982 raw14982Labels = mixedMoment B raw14982step0 raw14982step0Labels := by
      have hz : ∀ j, raw14982 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14982step0 = (fun i j => raw14982 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14982step0 raw14982; decide +kernel
      have hl : raw14982step0Labels = raw14982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14982 raw14982Labels permutation434 hz
    mixedMoment B raw14982step0 raw14982step0Labels = mixedMoment B raw14982step1 raw14982step1Labels := by
      have ha : raw14982step1 = (fun i j => raw14982step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14982step1 raw14982step0; decide +kernel
      have hl : raw14982step1Labels = raw14982step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14982step0 raw14982step0Labels permutation32 permutation6
    mixedMoment B raw14982step1 raw14982step1Labels = mixedMoment B raw14982step2 raw14982step2Labels := by
      have ha : raw14982step2 = raw14982step1 := by apply Matrix.ext; unfold raw14982step2 raw14982step1; decide +kernel
      have hl : raw14982step1Labels = labelEmbedding9 ∘ raw14982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14982step1 raw14982step1Labels raw14982step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw14983 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14983step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14983 raw14983Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw14983 raw14983Labels = mixedMoment B raw14983step0 raw14983step0Labels := by
      have ha : raw14983step0 = (fun i j => raw14983 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14983step0 raw14983; decide +kernel
      have hl : raw14983step0Labels = raw14983Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14983 raw14983Labels permutation158 permutation6
    mixedMoment B raw14983step0 raw14983step0Labels = mixedMoment B raw14983step1 raw14983step1Labels := by
      have ha : raw14983step1 = raw14983step0 := by apply Matrix.ext; unfold raw14983step1 raw14983step0; decide +kernel
      have hl : raw14983step0Labels = labelEmbedding9 ∘ raw14983step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14983step0 raw14983step0Labels raw14983step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw14984 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14984step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14984 raw14984Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw14984 raw14984Labels = mixedMoment B raw14984step0 raw14984step0Labels := by
      have hz : ∀ j, raw14984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14984step0 = (fun i j => raw14984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14984step0 raw14984; decide +kernel
      have hl : raw14984step0Labels = raw14984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14984 raw14984Labels permutation434 hz
    mixedMoment B raw14984step0 raw14984step0Labels = mixedMoment B raw14984step1 raw14984step1Labels := by
      have ha : raw14984step1 = (fun i j => raw14984step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14984step1 raw14984step0; decide +kernel
      have hl : raw14984step1Labels = raw14984step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14984step0 raw14984step0Labels permutation32 permutation6
    mixedMoment B raw14984step1 raw14984step1Labels = mixedMoment B raw14984step2 raw14984step2Labels := by
      have ha : raw14984step2 = raw14984step1 := by apply Matrix.ext; unfold raw14984step2 raw14984step1; decide +kernel
      have hl : raw14984step1Labels = labelEmbedding9 ∘ raw14984step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14984step1 raw14984step1Labels raw14984step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw14985 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14985 raw14985Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw14985 raw14985Labels = mixedMoment B raw14985step0 raw14985step0Labels := by
      have hz : ∀ j, raw14985 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14985step0 = (fun i j => raw14985 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14985step0 raw14985; decide +kernel
      have hl : raw14985step0Labels = raw14985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14985 raw14985Labels permutation434 hz
    mixedMoment B raw14985step0 raw14985step0Labels = mixedMoment B raw14985step1 raw14985step1Labels := by
      have ha : raw14985step1 = (fun i j => raw14985step0 (permutation133 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14985step1 raw14985step0; decide +kernel
      have hl : raw14985step1Labels = raw14985step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14985step0 raw14985step0Labels permutation133 permutation2
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw14986 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14986step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14986 raw14986Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw14986 raw14986Labels = mixedMoment B raw14986step0 raw14986step0Labels := by
      have ha : raw14986step0 = (fun i j => raw14986 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14986step0 raw14986; decide +kernel
      have hl : raw14986step0Labels = raw14986Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14986 raw14986Labels permutation152 permutation6
    mixedMoment B raw14986step0 raw14986step0Labels = mixedMoment B raw14986step1 raw14986step1Labels := by
      have ha : raw14986step1 = raw14986step0 := by apply Matrix.ext; unfold raw14986step1 raw14986step0; decide +kernel
      have hl : raw14986step0Labels = labelEmbedding9 ∘ raw14986step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14986step0 raw14986step0Labels raw14986step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw14987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -3, 1], ![-2, 0, 2]]
def raw14987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw14987step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14987step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw14987step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14987step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw14987step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14987 raw14987Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw14987 raw14987Labels = mixedMoment B raw14987step0 raw14987step0Labels := by
      have hz : ∀ j, raw14987 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14987step0 = (fun i j => raw14987 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14987step0 raw14987; decide +kernel
      have hl : raw14987step0Labels = raw14987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14987 raw14987Labels permutation434 hz
    mixedMoment B raw14987step0 raw14987step0Labels = mixedMoment B raw14987step1 raw14987step1Labels := by
      have hz : ∀ j, raw14987step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14987step1 = (fun i j => raw14987step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14987step1 raw14987step0; decide +kernel
      have hl : raw14987step1Labels = raw14987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14987step0 raw14987step0Labels permutation80 hz
    mixedMoment B raw14987step1 raw14987step1Labels = mixedMoment B raw14987step2 raw14987step2Labels := by
      have ha : raw14987step2 = (fun i j => raw14987step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14987step2 raw14987step1; decide +kernel
      have hl : raw14987step2Labels = raw14987step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14987step1 raw14987step1Labels permutation9 permutation4
    mixedMoment B raw14987step2 raw14987step2Labels = mixedMoment B raw14987step3 raw14987step3Labels := by
      have ha : raw14987step3 = -raw14987step2 := by apply Matrix.ext; change ∀ i j, raw14987step3 i j = -(raw14987step2 i j); unfold raw14987step3 raw14987step2; decide +kernel
      have hl : raw14987step3Labels = raw14987step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14987step3 raw14987step3Labels = mixedMoment B raw14987step4 raw14987step4Labels := by
      have ha : raw14987step4 = raw14987step3 := by apply Matrix.ext; unfold raw14987step4 raw14987step3; decide +kernel
      have hl : raw14987step3Labels = labelEmbedding7 ∘ raw14987step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14987step3 raw14987step3Labels raw14987step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw14988 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -3, 1], ![-2, 0, 2]]
def raw14988step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14988step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14988step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14988step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14988step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14988 raw14988Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw14988 raw14988Labels = mixedMoment B raw14988step0 raw14988step0Labels := by
      have hz : ∀ j, raw14988 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14988step0 = (fun i j => raw14988 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14988step0 raw14988; decide +kernel
      have hl : raw14988step0Labels = raw14988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14988 raw14988Labels permutation434 hz
    mixedMoment B raw14988step0 raw14988step0Labels = mixedMoment B raw14988step1 raw14988step1Labels := by
      have hz : ∀ j, raw14988step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14988step1 = (fun i j => raw14988step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14988step1 raw14988step0; decide +kernel
      have hl : raw14988step1Labels = raw14988step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14988step0 raw14988step0Labels permutation80 hz
    mixedMoment B raw14988step1 raw14988step1Labels = mixedMoment B raw14988step2 raw14988step2Labels := by
      have ha : raw14988step2 = (fun i j => raw14988step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14988step2 raw14988step1; decide +kernel
      have hl : raw14988step2Labels = raw14988step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14988step1 raw14988step1Labels permutation25 permutation5
    mixedMoment B raw14988step2 raw14988step2Labels = mixedMoment B raw14988step3 raw14988step3Labels := by
      have ha : raw14988step3 = raw14988step2 := by apply Matrix.ext; unfold raw14988step3 raw14988step2; decide +kernel
      have hl : raw14988step2Labels = labelEmbedding8 ∘ raw14988step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14988step2 raw14988step2Labels raw14988step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw14989 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw14989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14989step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14989step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14989 raw14989Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw14989 raw14989Labels = mixedMoment B raw14989step0 raw14989step0Labels := by
      have hz : ∀ j, raw14989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14989step0 = (fun i j => raw14989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14989step0 raw14989; decide +kernel
      have hl : raw14989step0Labels = raw14989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14989 raw14989Labels permutation346 hz
    mixedMoment B raw14989step0 raw14989step0Labels = mixedMoment B raw14989step1 raw14989step1Labels := by
      have ha : raw14989step1 = (fun i j => raw14989step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14989step1 raw14989step0; decide +kernel
      have hl : raw14989step1Labels = raw14989step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14989step0 raw14989step0Labels permutation115 permutation5
    mixedMoment B raw14989step1 raw14989step1Labels = mixedMoment B raw14989step2 raw14989step2Labels := by
      have ha : raw14989step2 = raw14989step1 := by apply Matrix.ext; unfold raw14989step2 raw14989step1; decide +kernel
      have hl : raw14989step1Labels = labelEmbedding8 ∘ raw14989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14989step1 raw14989step1Labels raw14989step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw14990 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw14990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw14990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -3, 1], ![-3, 1, 2]]
def raw14990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw14990step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14990step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw14990step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14990 raw14990Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw14990 raw14990Labels = mixedMoment B raw14990step0 raw14990step0Labels := by
      have hz : ∀ j, raw14990 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14990step0 = (fun i j => raw14990 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14990step0 raw14990; decide +kernel
      have hl : raw14990step0Labels = raw14990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14990 raw14990Labels permutation434 hz
    mixedMoment B raw14990step0 raw14990step0Labels = mixedMoment B raw14990step1 raw14990step1Labels := by
      have hz : ∀ j, raw14990step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14990step1 = (fun i j => raw14990step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14990step1 raw14990step0; decide +kernel
      have hl : raw14990step1Labels = raw14990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14990step0 raw14990step0Labels permutation80 hz
    mixedMoment B raw14990step1 raw14990step1Labels = mixedMoment B raw14990step2 raw14990step2Labels := by
      have ha : raw14990step2 = (fun i j => raw14990step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14990step2 raw14990step1; decide +kernel
      have hl : raw14990step2Labels = raw14990step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14990step1 raw14990step1Labels permutation23 permutation5
    mixedMoment B raw14990step2 raw14990step2Labels = mixedMoment B raw14990step3 raw14990step3Labels := by
      have ha : raw14990step3 = raw14990step2 := by apply Matrix.ext; unfold raw14990step3 raw14990step2; decide +kernel
      have hl : raw14990step2Labels = labelEmbedding8 ∘ raw14990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14990step2 raw14990step2Labels raw14990step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw14991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw14991step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14991step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14991step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14991step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14991step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14991step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14991step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14991 raw14991Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw14991 raw14991Labels = mixedMoment B raw14991step0 raw14991step0Labels := by
      have hz : ∀ j, raw14991 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14991step0 = (fun i j => raw14991 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14991step0 raw14991; decide +kernel
      have hl : raw14991step0Labels = raw14991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14991 raw14991Labels permutation434 hz
    mixedMoment B raw14991step0 raw14991step0Labels = mixedMoment B raw14991step1 raw14991step1Labels := by
      have hz : ∀ j, raw14991step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14991step1 = (fun i j => raw14991step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14991step1 raw14991step0; decide +kernel
      have hl : raw14991step1Labels = raw14991step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14991step0 raw14991step0Labels permutation80 hz
    mixedMoment B raw14991step1 raw14991step1Labels = mixedMoment B raw14991step2 raw14991step2Labels := by
      have ha : raw14991step2 = (fun i j => raw14991step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14991step2 raw14991step1; decide +kernel
      have hl : raw14991step2Labels = raw14991step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14991step1 raw14991step1Labels permutation9 permutation4
    mixedMoment B raw14991step2 raw14991step2Labels = mixedMoment B raw14991step3 raw14991step3Labels := by
      have ha : raw14991step3 = -raw14991step2 := by apply Matrix.ext; change ∀ i j, raw14991step3 i j = -(raw14991step2 i j); unfold raw14991step3 raw14991step2; decide +kernel
      have hl : raw14991step3Labels = raw14991step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14991step3 raw14991step3Labels = mixedMoment B raw14991step4 raw14991step4Labels := by
      have ha : raw14991step4 = raw14991step3 := by apply Matrix.ext; unfold raw14991step4 raw14991step3; decide +kernel
      have hl : raw14991step3Labels = labelEmbedding7 ∘ raw14991step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14991step3 raw14991step3Labels raw14991step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw14992 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw14992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14992step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14992step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14992step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14992step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14992 raw14992Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw14992 raw14992Labels = mixedMoment B raw14992step0 raw14992step0Labels := by
      have hz : ∀ j, raw14992 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14992step0 = (fun i j => raw14992 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14992step0 raw14992; decide +kernel
      have hl : raw14992step0Labels = raw14992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14992 raw14992Labels permutation434 hz
    mixedMoment B raw14992step0 raw14992step0Labels = mixedMoment B raw14992step1 raw14992step1Labels := by
      have hz : ∀ j, raw14992step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14992step1 = (fun i j => raw14992step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14992step1 raw14992step0; decide +kernel
      have hl : raw14992step1Labels = raw14992step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14992step0 raw14992step0Labels permutation80 hz
    mixedMoment B raw14992step1 raw14992step1Labels = mixedMoment B raw14992step2 raw14992step2Labels := by
      have ha : raw14992step2 = (fun i j => raw14992step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14992step2 raw14992step1; decide +kernel
      have hl : raw14992step2Labels = raw14992step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14992step1 raw14992step1Labels permutation9 permutation4
    mixedMoment B raw14992step2 raw14992step2Labels = mixedMoment B raw14992step3 raw14992step3Labels := by
      have ha : raw14992step3 = -raw14992step2 := by apply Matrix.ext; change ∀ i j, raw14992step3 i j = -(raw14992step2 i j); unfold raw14992step3 raw14992step2; decide +kernel
      have hl : raw14992step3Labels = raw14992step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14992step3 raw14992step3Labels = mixedMoment B raw14992step4 raw14992step4Labels := by
      have ha : raw14992step4 = raw14992step3 := by apply Matrix.ext; unfold raw14992step4 raw14992step3; decide +kernel
      have hl : raw14992step3Labels = labelEmbedding7 ∘ raw14992step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14992step3 raw14992step3Labels raw14992step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw14993 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw14993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw14993step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14993step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14993step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw14993step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14993 raw14993Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw14993 raw14993Labels = mixedMoment B raw14993step0 raw14993step0Labels := by
      have hz : ∀ j, raw14993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14993step0 = (fun i j => raw14993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14993step0 raw14993; decide +kernel
      have hl : raw14993step0Labels = raw14993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14993 raw14993Labels permutation346 hz
    mixedMoment B raw14993step0 raw14993step0Labels = mixedMoment B raw14993step1 raw14993step1Labels := by
      have ha : raw14993step1 = (fun i j => raw14993step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14993step1 raw14993step0; decide +kernel
      have hl : raw14993step1Labels = raw14993step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14993step0 raw14993step0Labels permutation39 permutation4
    mixedMoment B raw14993step1 raw14993step1Labels = mixedMoment B raw14993step2 raw14993step2Labels := by
      have ha : raw14993step2 = -raw14993step1 := by apply Matrix.ext; change ∀ i j, raw14993step2 i j = -(raw14993step1 i j); unfold raw14993step2 raw14993step1; decide +kernel
      have hl : raw14993step2Labels = raw14993step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14993step2 raw14993step2Labels = mixedMoment B raw14993step3 raw14993step3Labels := by
      have ha : raw14993step3 = raw14993step2 := by apply Matrix.ext; unfold raw14993step3 raw14993step2; decide +kernel
      have hl : raw14993step2Labels = labelEmbedding7 ∘ raw14993step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14993step2 raw14993step2Labels raw14993step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw14994 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw14994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw14994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2]]
def raw14994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14994step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14994step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14994step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14994 raw14994Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw14994 raw14994Labels = mixedMoment B raw14994step0 raw14994step0Labels := by
      have hz : ∀ j, raw14994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14994step0 = (fun i j => raw14994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14994step0 raw14994; decide +kernel
      have hl : raw14994step0Labels = raw14994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14994 raw14994Labels permutation434 hz
    mixedMoment B raw14994step0 raw14994step0Labels = mixedMoment B raw14994step1 raw14994step1Labels := by
      have hz : ∀ j, raw14994step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14994step1 = (fun i j => raw14994step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14994step1 raw14994step0; decide +kernel
      have hl : raw14994step1Labels = raw14994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14994step0 raw14994step0Labels permutation80 hz
    mixedMoment B raw14994step1 raw14994step1Labels = mixedMoment B raw14994step2 raw14994step2Labels := by
      have ha : raw14994step2 = (fun i j => raw14994step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14994step2 raw14994step1; decide +kernel
      have hl : raw14994step2Labels = raw14994step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14994step1 raw14994step1Labels permutation8 permutation6
    mixedMoment B raw14994step2 raw14994step2Labels = mixedMoment B raw14994step3 raw14994step3Labels := by
      have ha : raw14994step3 = raw14994step2 := by apply Matrix.ext; unfold raw14994step3 raw14994step2; decide +kernel
      have hl : raw14994step2Labels = labelEmbedding9 ∘ raw14994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14994step2 raw14994step2Labels raw14994step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw14995 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14995step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14995step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14995step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14995step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14995step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14995step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14995 raw14995Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw14995 raw14995Labels = mixedMoment B raw14995step0 raw14995step0Labels := by
      have hz : ∀ j, raw14995 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14995step0 = (fun i j => raw14995 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14995step0 raw14995; decide +kernel
      have hl : raw14995step0Labels = raw14995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14995 raw14995Labels permutation434 hz
    mixedMoment B raw14995step0 raw14995step0Labels = mixedMoment B raw14995step1 raw14995step1Labels := by
      have hz : ∀ j, raw14995step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14995step1 = (fun i j => raw14995step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14995step1 raw14995step0; decide +kernel
      have hl : raw14995step1Labels = raw14995step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14995step0 raw14995step0Labels permutation80 hz
    mixedMoment B raw14995step1 raw14995step1Labels = mixedMoment B raw14995step2 raw14995step2Labels := by
      have ha : raw14995step2 = (fun i j => raw14995step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14995step2 raw14995step1; decide +kernel
      have hl : raw14995step2Labels = raw14995step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14995step1 raw14995step1Labels permutation31 permutation7
    mixedMoment B raw14995step2 raw14995step2Labels = mixedMoment B raw14995step3 raw14995step3Labels := by
      have ha : raw14995step3 = -raw14995step2 := by apply Matrix.ext; change ∀ i j, raw14995step3 i j = -(raw14995step2 i j); unfold raw14995step3 raw14995step2; decide +kernel
      have hl : raw14995step3Labels = raw14995step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14995step3 raw14995step3Labels = mixedMoment B raw14995step4 raw14995step4Labels := by
      have ha : raw14995step4 = raw14995step3 := by apply Matrix.ext; unfold raw14995step4 raw14995step3; decide +kernel
      have hl : raw14995step3Labels = labelEmbedding1 ∘ raw14995step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14995step3 raw14995step3Labels raw14995step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw14996 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14996step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14996step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14996 raw14996Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw14996 raw14996Labels = mixedMoment B raw14996step0 raw14996step0Labels := by
      have hz : ∀ j, raw14996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14996step0 = (fun i j => raw14996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14996step0 raw14996; decide +kernel
      have hl : raw14996step0Labels = raw14996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14996 raw14996Labels permutation346 hz
    mixedMoment B raw14996step0 raw14996step0Labels = mixedMoment B raw14996step1 raw14996step1Labels := by
      have ha : raw14996step1 = (fun i j => raw14996step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14996step1 raw14996step0; decide +kernel
      have hl : raw14996step1Labels = raw14996step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14996step0 raw14996step0Labels permutation151 permutation7
    mixedMoment B raw14996step1 raw14996step1Labels = mixedMoment B raw14996step2 raw14996step2Labels := by
      have ha : raw14996step2 = -raw14996step1 := by apply Matrix.ext; change ∀ i j, raw14996step2 i j = -(raw14996step1 i j); unfold raw14996step2 raw14996step1; decide +kernel
      have hl : raw14996step2Labels = raw14996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14996step2 raw14996step2Labels = mixedMoment B raw14996step3 raw14996step3Labels := by
      have ha : raw14996step3 = raw14996step2 := by apply Matrix.ext; unfold raw14996step3 raw14996step2; decide +kernel
      have hl : raw14996step2Labels = labelEmbedding1 ∘ raw14996step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14996step2 raw14996step2Labels raw14996step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw14997 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2]]
def raw14997step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14997step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14997step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14997step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14997 raw14997Labels = mixedMoment B node3861 node3861Labels := by
  calc
    mixedMoment B raw14997 raw14997Labels = mixedMoment B raw14997step0 raw14997step0Labels := by
      have hz : ∀ j, raw14997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14997step0 = (fun i j => raw14997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14997step0 raw14997; decide +kernel
      have hl : raw14997step0Labels = raw14997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14997 raw14997Labels permutation434 hz
    mixedMoment B raw14997step0 raw14997step0Labels = mixedMoment B raw14997step1 raw14997step1Labels := by
      have hz : ∀ j, raw14997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14997step1 = (fun i j => raw14997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14997step1 raw14997step0; decide +kernel
      have hl : raw14997step1Labels = raw14997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14997step0 raw14997step0Labels permutation80 hz
    mixedMoment B raw14997step1 raw14997step1Labels = mixedMoment B raw14997step2 raw14997step2Labels := by
      have ha : raw14997step2 = (fun i j => raw14997step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14997step2 raw14997step1; decide +kernel
      have hl : raw14997step2Labels = raw14997step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14997step1 raw14997step1Labels permutation31 permutation7
    mixedMoment B raw14997step2 raw14997step2Labels = mixedMoment B raw14997step3 raw14997step3Labels := by
      have ha : raw14997step3 = -raw14997step2 := by apply Matrix.ext; change ∀ i j, raw14997step3 i j = -(raw14997step2 i j); unfold raw14997step3 raw14997step2; decide +kernel
      have hl : raw14997step3Labels = raw14997step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14997step3 raw14997step3Labels = mixedMoment B raw14997step4 raw14997step4Labels := by
      have ha : raw14997step4 = raw14997step3 := by apply Matrix.ext; unfold raw14997step4 raw14997step3; decide +kernel
      have hl : raw14997step3Labels = labelEmbedding1 ∘ raw14997step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14997step3 raw14997step3Labels raw14997step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3861 node3861Labels := by rfl

def raw14998 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -2, 1], ![-3, 1, 2]]
def raw14998step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14998step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14998step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14998step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14998 raw14998Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw14998 raw14998Labels = mixedMoment B raw14998step0 raw14998step0Labels := by
      have hz : ∀ j, raw14998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14998step0 = (fun i j => raw14998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14998step0 raw14998; decide +kernel
      have hl : raw14998step0Labels = raw14998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14998 raw14998Labels permutation434 hz
    mixedMoment B raw14998step0 raw14998step0Labels = mixedMoment B raw14998step1 raw14998step1Labels := by
      have hz : ∀ j, raw14998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14998step1 = (fun i j => raw14998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14998step1 raw14998step0; decide +kernel
      have hl : raw14998step1Labels = raw14998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14998step0 raw14998step0Labels permutation80 hz
    mixedMoment B raw14998step1 raw14998step1Labels = mixedMoment B raw14998step2 raw14998step2Labels := by
      have ha : raw14998step2 = (fun i j => raw14998step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14998step2 raw14998step1; decide +kernel
      have hl : raw14998step2Labels = raw14998step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14998step1 raw14998step1Labels permutation31 permutation7
    mixedMoment B raw14998step2 raw14998step2Labels = mixedMoment B raw14998step3 raw14998step3Labels := by
      have ha : raw14998step3 = -raw14998step2 := by apply Matrix.ext; change ∀ i j, raw14998step3 i j = -(raw14998step2 i j); unfold raw14998step3 raw14998step2; decide +kernel
      have hl : raw14998step3Labels = raw14998step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14998step3 raw14998step3Labels = mixedMoment B raw14998step4 raw14998step4Labels := by
      have ha : raw14998step4 = raw14998step3 := by apply Matrix.ext; unfold raw14998step4 raw14998step3; decide +kernel
      have hl : raw14998step3Labels = labelEmbedding1 ∘ raw14998step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14998step3 raw14998step3Labels raw14998step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw14999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14999step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw14999step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14999step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw14999step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14999step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw14999step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14999 raw14999Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw14999 raw14999Labels = mixedMoment B raw14999step0 raw14999step0Labels := by
      have hz : ∀ j, raw14999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14999step0 = (fun i j => raw14999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14999step0 raw14999; decide +kernel
      have hl : raw14999step0Labels = raw14999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14999 raw14999Labels permutation434 hz
    mixedMoment B raw14999step0 raw14999step0Labels = mixedMoment B raw14999step1 raw14999step1Labels := by
      have hz : ∀ j, raw14999step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14999step1 = (fun i j => raw14999step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14999step1 raw14999step0; decide +kernel
      have hl : raw14999step1Labels = raw14999step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14999step0 raw14999step0Labels permutation80 hz
    mixedMoment B raw14999step1 raw14999step1Labels = mixedMoment B raw14999step2 raw14999step2Labels := by
      have ha : raw14999step2 = (fun i j => raw14999step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14999step2 raw14999step1; decide +kernel
      have hl : raw14999step2Labels = raw14999step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14999step1 raw14999step1Labels permutation12 permutation5
    mixedMoment B raw14999step2 raw14999step2Labels = mixedMoment B raw14999step3 raw14999step3Labels := by
      have ha : raw14999step3 = -raw14999step2 := by apply Matrix.ext; change ∀ i j, raw14999step3 i j = -(raw14999step2 i j); unfold raw14999step3 raw14999step2; decide +kernel
      have hl : raw14999step3Labels = raw14999step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14999step3 raw14999step3Labels = mixedMoment B raw14999step4 raw14999step4Labels := by
      have ha : raw14999step4 = raw14999step3 := by apply Matrix.ext; unfold raw14999step4 raw14999step3; decide +kernel
      have hl : raw14999step3Labels = labelEmbedding1 ∘ raw14999step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14999step3 raw14999step3Labels raw14999step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw15000 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15000step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15000 raw15000Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw15000 raw15000Labels = mixedMoment B raw15000step0 raw15000step0Labels := by
      have hz : ∀ j, raw15000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15000step0 = (fun i j => raw15000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15000step0 raw15000; decide +kernel
      have hl : raw15000step0Labels = raw15000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15000 raw15000Labels permutation346 hz
    mixedMoment B raw15000step0 raw15000step0Labels = mixedMoment B raw15000step1 raw15000step1Labels := by
      have ha : raw15000step1 = (fun i j => raw15000step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15000step1 raw15000step0; decide +kernel
      have hl : raw15000step1Labels = raw15000step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15000step0 raw15000step0Labels permutation151 permutation7
    mixedMoment B raw15000step1 raw15000step1Labels = mixedMoment B raw15000step2 raw15000step2Labels := by
      have ha : raw15000step2 = -raw15000step1 := by apply Matrix.ext; change ∀ i j, raw15000step2 i j = -(raw15000step1 i j); unfold raw15000step2 raw15000step1; decide +kernel
      have hl : raw15000step2Labels = raw15000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15000step2 raw15000step2Labels = mixedMoment B raw15000step3 raw15000step3Labels := by
      have ha : raw15000step3 = raw15000step2 := by apply Matrix.ext; unfold raw15000step3 raw15000step2; decide +kernel
      have hl : raw15000step2Labels = labelEmbedding1 ∘ raw15000step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15000step2 raw15000step2Labels raw15000step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw15001 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2]]
def raw15001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15001step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15001step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15001step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15001 raw15001Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw15001 raw15001Labels = mixedMoment B raw15001step0 raw15001step0Labels := by
      have hz : ∀ j, raw15001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15001step0 = (fun i j => raw15001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15001step0 raw15001; decide +kernel
      have hl : raw15001step0Labels = raw15001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15001 raw15001Labels permutation434 hz
    mixedMoment B raw15001step0 raw15001step0Labels = mixedMoment B raw15001step1 raw15001step1Labels := by
      have hz : ∀ j, raw15001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15001step1 = (fun i j => raw15001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15001step1 raw15001step0; decide +kernel
      have hl : raw15001step1Labels = raw15001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15001step0 raw15001step0Labels permutation80 hz
    mixedMoment B raw15001step1 raw15001step1Labels = mixedMoment B raw15001step2 raw15001step2Labels := by
      have ha : raw15001step2 = (fun i j => raw15001step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15001step2 raw15001step1; decide +kernel
      have hl : raw15001step2Labels = raw15001step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15001step1 raw15001step1Labels permutation31 permutation7
    mixedMoment B raw15001step2 raw15001step2Labels = mixedMoment B raw15001step3 raw15001step3Labels := by
      have ha : raw15001step3 = -raw15001step2 := by apply Matrix.ext; change ∀ i j, raw15001step3 i j = -(raw15001step2 i j); unfold raw15001step3 raw15001step2; decide +kernel
      have hl : raw15001step3Labels = raw15001step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15001step3 raw15001step3Labels = mixedMoment B raw15001step4 raw15001step4Labels := by
      have ha : raw15001step4 = raw15001step3 := by apply Matrix.ext; unfold raw15001step4 raw15001step3; decide +kernel
      have hl : raw15001step3Labels = labelEmbedding1 ∘ raw15001step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15001step3 raw15001step3Labels raw15001step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw15002 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw15002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw15002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -2, 1], ![-3, 1, 2]]
def raw15002step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15002step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15002step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15002step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15002 raw15002Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw15002 raw15002Labels = mixedMoment B raw15002step0 raw15002step0Labels := by
      have hz : ∀ j, raw15002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15002step0 = (fun i j => raw15002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15002step0 raw15002; decide +kernel
      have hl : raw15002step0Labels = raw15002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15002 raw15002Labels permutation434 hz
    mixedMoment B raw15002step0 raw15002step0Labels = mixedMoment B raw15002step1 raw15002step1Labels := by
      have hz : ∀ j, raw15002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15002step1 = (fun i j => raw15002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15002step1 raw15002step0; decide +kernel
      have hl : raw15002step1Labels = raw15002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15002step0 raw15002step0Labels permutation80 hz
    mixedMoment B raw15002step1 raw15002step1Labels = mixedMoment B raw15002step2 raw15002step2Labels := by
      have ha : raw15002step2 = (fun i j => raw15002step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15002step2 raw15002step1; decide +kernel
      have hl : raw15002step2Labels = raw15002step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15002step1 raw15002step1Labels permutation31 permutation7
    mixedMoment B raw15002step2 raw15002step2Labels = mixedMoment B raw15002step3 raw15002step3Labels := by
      have ha : raw15002step3 = -raw15002step2 := by apply Matrix.ext; change ∀ i j, raw15002step3 i j = -(raw15002step2 i j); unfold raw15002step3 raw15002step2; decide +kernel
      have hl : raw15002step3Labels = raw15002step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15002step3 raw15002step3Labels = mixedMoment B raw15002step4 raw15002step4Labels := by
      have ha : raw15002step4 = raw15002step3 := by apply Matrix.ext; unfold raw15002step4 raw15002step3; decide +kernel
      have hl : raw15002step3Labels = labelEmbedding1 ∘ raw15002step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15002step3 raw15002step3Labels raw15002step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw15003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15003 raw15003Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw15003 raw15003Labels = mixedMoment B raw15003step0 raw15003step0Labels := by
      have hz : ∀ j, raw15003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15003step0 = (fun i j => raw15003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15003step0 raw15003; decide +kernel
      have hl : raw15003step0Labels = raw15003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15003 raw15003Labels permutation434 hz
    mixedMoment B raw15003step0 raw15003step0Labels = mixedMoment B raw15003step1 raw15003step1Labels := by
      have ha : raw15003step1 = (fun i j => raw15003step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15003step1 raw15003step0; decide +kernel
      have hl : raw15003step1Labels = raw15003step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15003step0 raw15003step0Labels permutation50 permutation5
    mixedMoment B raw15003step1 raw15003step1Labels = mixedMoment B raw15003step2 raw15003step2Labels := by
      have ha : raw15003step2 = -raw15003step1 := by apply Matrix.ext; change ∀ i j, raw15003step2 i j = -(raw15003step1 i j); unfold raw15003step2 raw15003step1; decide +kernel
      have hl : raw15003step2Labels = raw15003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15003step2 raw15003step2Labels = mixedMoment B raw15003step3 raw15003step3Labels := by
      have ha : raw15003step3 = raw15003step2 := by apply Matrix.ext; unfold raw15003step3 raw15003step2; decide +kernel
      have hl : raw15003step2Labels = labelEmbedding1 ∘ raw15003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15003step2 raw15003step2Labels raw15003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw15004 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw15004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15004step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15004step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15004step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15004 raw15004Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw15004 raw15004Labels = mixedMoment B raw15004step0 raw15004step0Labels := by
      have hz : ∀ j, raw15004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15004step0 = (fun i j => raw15004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15004step0 raw15004; decide +kernel
      have hl : raw15004step0Labels = raw15004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15004 raw15004Labels permutation434 hz
    mixedMoment B raw15004step0 raw15004step0Labels = mixedMoment B raw15004step1 raw15004step1Labels := by
      have ha : raw15004step1 = (fun i j => raw15004step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15004step1 raw15004step0; decide +kernel
      have hl : raw15004step1Labels = raw15004step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15004step0 raw15004step0Labels permutation151 permutation7
    mixedMoment B raw15004step1 raw15004step1Labels = mixedMoment B raw15004step2 raw15004step2Labels := by
      have ha : raw15004step2 = -raw15004step1 := by apply Matrix.ext; change ∀ i j, raw15004step2 i j = -(raw15004step1 i j); unfold raw15004step2 raw15004step1; decide +kernel
      have hl : raw15004step2Labels = raw15004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15004step2 raw15004step2Labels = mixedMoment B raw15004step3 raw15004step3Labels := by
      have ha : raw15004step3 = raw15004step2 := by apply Matrix.ext; unfold raw15004step3 raw15004step2; decide +kernel
      have hl : raw15004step2Labels = labelEmbedding1 ∘ raw15004step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15004step2 raw15004step2Labels raw15004step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw15005 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15005step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15005step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15005step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15005 raw15005Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw15005 raw15005Labels = mixedMoment B raw15005step0 raw15005step0Labels := by
      have ha : raw15005step0 = (fun i j => raw15005 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15005step0 raw15005; decide +kernel
      have hl : raw15005step0Labels = raw15005Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15005 raw15005Labels permutation688 permutation7
    mixedMoment B raw15005step0 raw15005step0Labels = mixedMoment B raw15005step1 raw15005step1Labels := by
      have ha : raw15005step1 = -raw15005step0 := by apply Matrix.ext; change ∀ i j, raw15005step1 i j = -(raw15005step0 i j); unfold raw15005step1 raw15005step0; decide +kernel
      have hl : raw15005step1Labels = raw15005step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15005step1 raw15005step1Labels = mixedMoment B raw15005step2 raw15005step2Labels := by
      have ha : raw15005step2 = raw15005step1 := by apply Matrix.ext; unfold raw15005step2 raw15005step1; decide +kernel
      have hl : raw15005step1Labels = labelEmbedding1 ∘ raw15005step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15005step1 raw15005step1Labels raw15005step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw15006 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15006 raw15006Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw15006 raw15006Labels = mixedMoment B raw15006step0 raw15006step0Labels := by
      have hz : ∀ j, raw15006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15006step0 = (fun i j => raw15006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15006step0 raw15006; decide +kernel
      have hl : raw15006step0Labels = raw15006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15006 raw15006Labels permutation434 hz
    mixedMoment B raw15006step0 raw15006step0Labels = mixedMoment B raw15006step1 raw15006step1Labels := by
      have ha : raw15006step1 = (fun i j => raw15006step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15006step1 raw15006step0; decide +kernel
      have hl : raw15006step1Labels = raw15006step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15006step0 raw15006step0Labels permutation151 permutation7
    mixedMoment B raw15006step1 raw15006step1Labels = mixedMoment B raw15006step2 raw15006step2Labels := by
      have ha : raw15006step2 = -raw15006step1 := by apply Matrix.ext; change ∀ i j, raw15006step2 i j = -(raw15006step1 i j); unfold raw15006step2 raw15006step1; decide +kernel
      have hl : raw15006step2Labels = raw15006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15006step2 raw15006step2Labels = mixedMoment B raw15006step3 raw15006step3Labels := by
      have ha : raw15006step3 = raw15006step2 := by apply Matrix.ext; unfold raw15006step3 raw15006step2; decide +kernel
      have hl : raw15006step2Labels = labelEmbedding1 ∘ raw15006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15006step2 raw15006step2Labels raw15006step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw15007 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw15007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw15007step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15007step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15007step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15007step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15007 raw15007Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw15007 raw15007Labels = mixedMoment B raw15007step0 raw15007step0Labels := by
      have hz : ∀ j, raw15007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15007step0 = (fun i j => raw15007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15007step0 raw15007; decide +kernel
      have hl : raw15007step0Labels = raw15007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15007 raw15007Labels permutation434 hz
    mixedMoment B raw15007step0 raw15007step0Labels = mixedMoment B raw15007step1 raw15007step1Labels := by
      have ha : raw15007step1 = (fun i j => raw15007step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15007step1 raw15007step0; decide +kernel
      have hl : raw15007step1Labels = raw15007step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15007step0 raw15007step0Labels permutation151 permutation7
    mixedMoment B raw15007step1 raw15007step1Labels = mixedMoment B raw15007step2 raw15007step2Labels := by
      have ha : raw15007step2 = -raw15007step1 := by apply Matrix.ext; change ∀ i j, raw15007step2 i j = -(raw15007step1 i j); unfold raw15007step2 raw15007step1; decide +kernel
      have hl : raw15007step2Labels = raw15007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15007step2 raw15007step2Labels = mixedMoment B raw15007step3 raw15007step3Labels := by
      have ha : raw15007step3 = raw15007step2 := by apply Matrix.ext; unfold raw15007step3 raw15007step2; decide +kernel
      have hl : raw15007step2Labels = labelEmbedding1 ∘ raw15007step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15007step2 raw15007step2Labels raw15007step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw15008 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw15008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15008step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15008step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15008 raw15008Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw15008 raw15008Labels = mixedMoment B raw15008step0 raw15008step0Labels := by
      have ha : raw15008step0 = (fun i j => raw15008 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15008step0 raw15008; decide +kernel
      have hl : raw15008step0Labels = raw15008Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15008 raw15008Labels permutation682 permutation7
    mixedMoment B raw15008step0 raw15008step0Labels = mixedMoment B raw15008step1 raw15008step1Labels := by
      have ha : raw15008step1 = -raw15008step0 := by apply Matrix.ext; change ∀ i j, raw15008step1 i j = -(raw15008step0 i j); unfold raw15008step1 raw15008step0; decide +kernel
      have hl : raw15008step1Labels = raw15008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15008step1 raw15008step1Labels = mixedMoment B raw15008step2 raw15008step2Labels := by
      have ha : raw15008step2 = raw15008step1 := by apply Matrix.ext; unfold raw15008step2 raw15008step1; decide +kernel
      have hl : raw15008step1Labels = labelEmbedding1 ∘ raw15008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15008step1 raw15008step1Labels raw15008step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw15009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw15009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw15009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -3, 1], ![-2, 0, 2]]
def raw15009step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15009step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15009step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15009 raw15009Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw15009 raw15009Labels = mixedMoment B raw15009step0 raw15009step0Labels := by
      have hz : ∀ j, raw15009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15009step0 = (fun i j => raw15009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15009step0 raw15009; decide +kernel
      have hl : raw15009step0Labels = raw15009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15009 raw15009Labels permutation434 hz
    mixedMoment B raw15009step0 raw15009step0Labels = mixedMoment B raw15009step1 raw15009step1Labels := by
      have hz : ∀ j, raw15009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15009step1 = (fun i j => raw15009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15009step1 raw15009step0; decide +kernel
      have hl : raw15009step1Labels = raw15009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15009step0 raw15009step0Labels permutation80 hz
    mixedMoment B raw15009step1 raw15009step1Labels = mixedMoment B raw15009step2 raw15009step2Labels := by
      have ha : raw15009step2 = (fun i j => raw15009step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15009step2 raw15009step1; decide +kernel
      have hl : raw15009step2Labels = raw15009step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15009step1 raw15009step1Labels permutation23 permutation5
    mixedMoment B raw15009step2 raw15009step2Labels = mixedMoment B raw15009step3 raw15009step3Labels := by
      have ha : raw15009step3 = raw15009step2 := by apply Matrix.ext; unfold raw15009step3 raw15009step2; decide +kernel
      have hl : raw15009step2Labels = labelEmbedding1 ∘ raw15009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15009step2 raw15009step2Labels raw15009step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw15010 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw15010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw15010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -3, 1], ![-2, 0, 2]]
def raw15010step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15010step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15010step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15010 raw15010Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw15010 raw15010Labels = mixedMoment B raw15010step0 raw15010step0Labels := by
      have hz : ∀ j, raw15010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15010step0 = (fun i j => raw15010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15010step0 raw15010; decide +kernel
      have hl : raw15010step0Labels = raw15010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15010 raw15010Labels permutation434 hz
    mixedMoment B raw15010step0 raw15010step0Labels = mixedMoment B raw15010step1 raw15010step1Labels := by
      have hz : ∀ j, raw15010step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15010step1 = (fun i j => raw15010step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15010step1 raw15010step0; decide +kernel
      have hl : raw15010step1Labels = raw15010step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15010step0 raw15010step0Labels permutation80 hz
    mixedMoment B raw15010step1 raw15010step1Labels = mixedMoment B raw15010step2 raw15010step2Labels := by
      have ha : raw15010step2 = (fun i j => raw15010step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15010step2 raw15010step1; decide +kernel
      have hl : raw15010step2Labels = raw15010step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15010step1 raw15010step1Labels permutation25 permutation5
    mixedMoment B raw15010step2 raw15010step2Labels = mixedMoment B raw15010step3 raw15010step3Labels := by
      have ha : raw15010step3 = raw15010step2 := by apply Matrix.ext; unfold raw15010step3 raw15010step2; decide +kernel
      have hl : raw15010step2Labels = labelEmbedding1 ∘ raw15010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15010step2 raw15010step2Labels raw15010step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw15011 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw15011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw15011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15011step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15011step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15011 raw15011Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw15011 raw15011Labels = mixedMoment B raw15011step0 raw15011step0Labels := by
      have hz : ∀ j, raw15011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15011step0 = (fun i j => raw15011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15011step0 raw15011; decide +kernel
      have hl : raw15011step0Labels = raw15011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15011 raw15011Labels permutation346 hz
    mixedMoment B raw15011step0 raw15011step0Labels = mixedMoment B raw15011step1 raw15011step1Labels := by
      have ha : raw15011step1 = (fun i j => raw15011step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15011step1 raw15011step0; decide +kernel
      have hl : raw15011step1Labels = raw15011step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15011step0 raw15011step0Labels permutation115 permutation5
    mixedMoment B raw15011step1 raw15011step1Labels = mixedMoment B raw15011step2 raw15011step2Labels := by
      have ha : raw15011step2 = raw15011step1 := by apply Matrix.ext; unfold raw15011step2 raw15011step1; decide +kernel
      have hl : raw15011step1Labels = labelEmbedding1 ∘ raw15011step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15011step1 raw15011step1Labels raw15011step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw15012 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw15012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw15012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -3, 1], ![-3, 1, 2]]
def raw15012step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw15012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15012step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw15012step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15012 raw15012Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw15012 raw15012Labels = mixedMoment B raw15012step0 raw15012step0Labels := by
      have hz : ∀ j, raw15012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15012step0 = (fun i j => raw15012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15012step0 raw15012; decide +kernel
      have hl : raw15012step0Labels = raw15012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15012 raw15012Labels permutation434 hz
    mixedMoment B raw15012step0 raw15012step0Labels = mixedMoment B raw15012step1 raw15012step1Labels := by
      have hz : ∀ j, raw15012step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15012step1 = (fun i j => raw15012step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15012step1 raw15012step0; decide +kernel
      have hl : raw15012step1Labels = raw15012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15012step0 raw15012step0Labels permutation80 hz
    mixedMoment B raw15012step1 raw15012step1Labels = mixedMoment B raw15012step2 raw15012step2Labels := by
      have ha : raw15012step2 = (fun i j => raw15012step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15012step2 raw15012step1; decide +kernel
      have hl : raw15012step2Labels = raw15012step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15012step1 raw15012step1Labels permutation23 permutation5
    mixedMoment B raw15012step2 raw15012step2Labels = mixedMoment B raw15012step3 raw15012step3Labels := by
      have ha : raw15012step3 = raw15012step2 := by apply Matrix.ext; unfold raw15012step3 raw15012step2; decide +kernel
      have hl : raw15012step2Labels = labelEmbedding1 ∘ raw15012step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15012step2 raw15012step2Labels raw15012step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw15013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw15013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw15013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw15013step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw15013step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15013step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15013step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15013step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15013step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15013 raw15013Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw15013 raw15013Labels = mixedMoment B raw15013step0 raw15013step0Labels := by
      have hz : ∀ j, raw15013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15013step0 = (fun i j => raw15013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15013step0 raw15013; decide +kernel
      have hl : raw15013step0Labels = raw15013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15013 raw15013Labels permutation434 hz
    mixedMoment B raw15013step0 raw15013step0Labels = mixedMoment B raw15013step1 raw15013step1Labels := by
      have hz : ∀ j, raw15013step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15013step1 = (fun i j => raw15013step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15013step1 raw15013step0; decide +kernel
      have hl : raw15013step1Labels = raw15013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15013step0 raw15013step0Labels permutation80 hz
    mixedMoment B raw15013step1 raw15013step1Labels = mixedMoment B raw15013step2 raw15013step2Labels := by
      have ha : raw15013step2 = (fun i j => raw15013step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15013step2 raw15013step1; decide +kernel
      have hl : raw15013step2Labels = raw15013step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15013step1 raw15013step1Labels permutation9 permutation5
    mixedMoment B raw15013step2 raw15013step2Labels = mixedMoment B raw15013step3 raw15013step3Labels := by
      have ha : raw15013step3 = -raw15013step2 := by apply Matrix.ext; change ∀ i j, raw15013step3 i j = -(raw15013step2 i j); unfold raw15013step3 raw15013step2; decide +kernel
      have hl : raw15013step3Labels = raw15013step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15013step3 raw15013step3Labels = mixedMoment B raw15013step4 raw15013step4Labels := by
      have ha : raw15013step4 = raw15013step3 := by apply Matrix.ext; unfold raw15013step4 raw15013step3; decide +kernel
      have hl : raw15013step3Labels = labelEmbedding1 ∘ raw15013step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15013step3 raw15013step3Labels raw15013step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw15014 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw15014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw15014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw15014step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15014step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15014step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15014 raw15014Labels = mixedMoment B node4006 node4006Labels := by
  calc
    mixedMoment B raw15014 raw15014Labels = mixedMoment B raw15014step0 raw15014step0Labels := by
      have hz : ∀ j, raw15014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15014step0 = (fun i j => raw15014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15014step0 raw15014; decide +kernel
      have hl : raw15014step0Labels = raw15014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15014 raw15014Labels permutation434 hz
    mixedMoment B raw15014step0 raw15014step0Labels = mixedMoment B raw15014step1 raw15014step1Labels := by
      have hz : ∀ j, raw15014step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15014step1 = (fun i j => raw15014step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15014step1 raw15014step0; decide +kernel
      have hl : raw15014step1Labels = raw15014step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15014step0 raw15014step0Labels permutation80 hz
    mixedMoment B raw15014step1 raw15014step1Labels = mixedMoment B raw15014step2 raw15014step2Labels := by
      have ha : raw15014step2 = (fun i j => raw15014step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15014step2 raw15014step1; decide +kernel
      have hl : raw15014step2Labels = raw15014step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15014step1 raw15014step1Labels permutation25 permutation5
    mixedMoment B raw15014step2 raw15014step2Labels = mixedMoment B raw15014step3 raw15014step3Labels := by
      have ha : raw15014step3 = raw15014step2 := by apply Matrix.ext; unfold raw15014step3 raw15014step2; decide +kernel
      have hl : raw15014step2Labels = labelEmbedding1 ∘ raw15014step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15014step2 raw15014step2Labels raw15014step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4006 node4006Labels := by rfl

def raw15015 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw15015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw15015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw15015step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw15015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15015 raw15015Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw15015 raw15015Labels = mixedMoment B raw15015step0 raw15015step0Labels := by
      have hz : ∀ j, raw15015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15015step0 = (fun i j => raw15015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15015step0 raw15015; decide +kernel
      have hl : raw15015step0Labels = raw15015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15015 raw15015Labels permutation346 hz
    mixedMoment B raw15015step0 raw15015step0Labels = mixedMoment B raw15015step1 raw15015step1Labels := by
      have ha : raw15015step1 = (fun i j => raw15015step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15015step1 raw15015step0; decide +kernel
      have hl : raw15015step1Labels = raw15015step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15015step0 raw15015step0Labels permutation125 permutation5
    mixedMoment B raw15015step1 raw15015step1Labels = mixedMoment B raw15015step2 raw15015step2Labels := by
      have ha : raw15015step2 = raw15015step1 := by apply Matrix.ext; unfold raw15015step2 raw15015step1; decide +kernel
      have hl : raw15015step1Labels = labelEmbedding1 ∘ raw15015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15015step1 raw15015step1Labels raw15015step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4003 node4003Labels := by rfl

def raw15016 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2]]
def raw15016step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw15016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15016step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15016step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15016step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15016 raw15016Labels = mixedMoment B node4001 node4001Labels := by
  calc
    mixedMoment B raw15016 raw15016Labels = mixedMoment B raw15016step0 raw15016step0Labels := by
      have hz : ∀ j, raw15016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15016step0 = (fun i j => raw15016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15016step0 raw15016; decide +kernel
      have hl : raw15016step0Labels = raw15016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15016 raw15016Labels permutation434 hz
    mixedMoment B raw15016step0 raw15016step0Labels = mixedMoment B raw15016step1 raw15016step1Labels := by
      have hz : ∀ j, raw15016step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15016step1 = (fun i j => raw15016step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15016step1 raw15016step0; decide +kernel
      have hl : raw15016step1Labels = raw15016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15016step0 raw15016step0Labels permutation80 hz
    mixedMoment B raw15016step1 raw15016step1Labels = mixedMoment B raw15016step2 raw15016step2Labels := by
      have ha : raw15016step2 = (fun i j => raw15016step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15016step2 raw15016step1; decide +kernel
      have hl : raw15016step2Labels = raw15016step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15016step1 raw15016step1Labels permutation31 permutation7
    mixedMoment B raw15016step2 raw15016step2Labels = mixedMoment B raw15016step3 raw15016step3Labels := by
      have ha : raw15016step3 = -raw15016step2 := by apply Matrix.ext; change ∀ i j, raw15016step3 i j = -(raw15016step2 i j); unfold raw15016step3 raw15016step2; decide +kernel
      have hl : raw15016step3Labels = raw15016step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15016step3 raw15016step3Labels = mixedMoment B raw15016step4 raw15016step4Labels := by
      have ha : raw15016step4 = raw15016step3 := by apply Matrix.ext; unfold raw15016step4 raw15016step3; decide +kernel
      have hl : raw15016step3Labels = labelEmbedding1 ∘ raw15016step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15016step3 raw15016step3Labels raw15016step4Labels labelEmbedding1 hl
    _ = mixedMoment B node4001 node4001Labels := by rfl

def raw15017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15017step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15017step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15017step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15017step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15017 raw15017Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw15017 raw15017Labels = mixedMoment B raw15017step0 raw15017step0Labels := by
      have hz : ∀ j, raw15017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15017step0 = (fun i j => raw15017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15017step0 raw15017; decide +kernel
      have hl : raw15017step0Labels = raw15017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15017 raw15017Labels permutation346 hz
    mixedMoment B raw15017step0 raw15017step0Labels = mixedMoment B raw15017step1 raw15017step1Labels := by
      have ha : raw15017step1 = (fun i j => raw15017step0 (permutation62 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15017step1 raw15017step0; decide +kernel
      have hl : raw15017step1Labels = raw15017step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15017step0 raw15017step0Labels permutation62 permutation5
    mixedMoment B raw15017step1 raw15017step1Labels = mixedMoment B raw15017step2 raw15017step2Labels := by
      have ha : raw15017step2 = -raw15017step1 := by apply Matrix.ext; change ∀ i j, raw15017step2 i j = -(raw15017step1 i j); unfold raw15017step2 raw15017step1; decide +kernel
      have hl : raw15017step2Labels = raw15017step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15017step2 raw15017step2Labels = mixedMoment B raw15017step3 raw15017step3Labels := by
      have ha : raw15017step3 = raw15017step2 := by apply Matrix.ext; unfold raw15017step3 raw15017step2; decide +kernel
      have hl : raw15017step2Labels = labelEmbedding8 ∘ raw15017step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15017step2 raw15017step2Labels raw15017step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw15018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15018step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15018step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15018step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15018step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15018step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15018 raw15018Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw15018 raw15018Labels = mixedMoment B raw15018step0 raw15018step0Labels := by
      have ha : raw15018step0 = (fun i j => raw15018 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15018step0 raw15018; decide +kernel
      have hl : raw15018step0Labels = raw15018Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15018 raw15018Labels permutation683 permutation3
    mixedMoment B raw15018step0 raw15018step0Labels = mixedMoment B raw15018step1 raw15018step1Labels := by
      have ha : raw15018step1 = -raw15018step0 := by apply Matrix.ext; change ∀ i j, raw15018step1 i j = -(raw15018step0 i j); unfold raw15018step1 raw15018step0; decide +kernel
      have hl : raw15018step1Labels = raw15018step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15018step1 raw15018step1Labels = mixedMoment B raw15018step2 raw15018step2Labels := by
      have ha : raw15018step2 = raw15018step1 := by apply Matrix.ext; unfold raw15018step2 raw15018step1; decide +kernel
      have hl : raw15018step1Labels = labelEmbedding6 ∘ raw15018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15018step1 raw15018step1Labels raw15018step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw15019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15019step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15019step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15019step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15019step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15019 raw15019Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw15019 raw15019Labels = mixedMoment B raw15019step0 raw15019step0Labels := by
      have hz : ∀ j, raw15019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15019step0 = (fun i j => raw15019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15019step0 raw15019; decide +kernel
      have hl : raw15019step0Labels = raw15019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15019 raw15019Labels permutation346 hz
    mixedMoment B raw15019step0 raw15019step0Labels = mixedMoment B raw15019step1 raw15019step1Labels := by
      have ha : raw15019step1 = (fun i j => raw15019step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15019step1 raw15019step0; decide +kernel
      have hl : raw15019step1Labels = raw15019step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15019step0 raw15019step0Labels permutation146 permutation3
    mixedMoment B raw15019step1 raw15019step1Labels = mixedMoment B raw15019step2 raw15019step2Labels := by
      have ha : raw15019step2 = -raw15019step1 := by apply Matrix.ext; change ∀ i j, raw15019step2 i j = -(raw15019step1 i j); unfold raw15019step2 raw15019step1; decide +kernel
      have hl : raw15019step2Labels = raw15019step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15019step2 raw15019step2Labels = mixedMoment B raw15019step3 raw15019step3Labels := by
      have ha : raw15019step3 = raw15019step2 := by apply Matrix.ext; unfold raw15019step3 raw15019step2; decide +kernel
      have hl : raw15019step2Labels = labelEmbedding6 ∘ raw15019step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15019step2 raw15019step2Labels raw15019step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw15020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw15020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw15020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15020step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15020step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15020step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15020 raw15020Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw15020 raw15020Labels = mixedMoment B raw15020step0 raw15020step0Labels := by
      have hz : ∀ j, raw15020 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15020step0 = (fun i j => raw15020 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15020step0 raw15020; decide +kernel
      have hl : raw15020step0Labels = raw15020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15020 raw15020Labels permutation520 hz
    mixedMoment B raw15020step0 raw15020step0Labels = mixedMoment B raw15020step1 raw15020step1Labels := by
      have hz : ∀ j, raw15020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15020step1 = (fun i j => raw15020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15020step1 raw15020step0; decide +kernel
      have hl : raw15020step1Labels = raw15020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15020step0 raw15020step0Labels permutation80 hz
    mixedMoment B raw15020step1 raw15020step1Labels = mixedMoment B raw15020step2 raw15020step2Labels := by
      have ha : raw15020step2 = (fun i j => raw15020step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15020step2 raw15020step1; decide +kernel
      have hl : raw15020step2Labels = raw15020step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15020step1 raw15020step1Labels permutation31 permutation2
    mixedMoment B raw15020step2 raw15020step2Labels = mixedMoment B raw15020step3 raw15020step3Labels := by
      have ha : raw15020step3 = -raw15020step2 := by apply Matrix.ext; change ∀ i j, raw15020step3 i j = -(raw15020step2 i j); unfold raw15020step3 raw15020step2; decide +kernel
      have hl : raw15020step3Labels = raw15020step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw15021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15021step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15021step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15021step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15021step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15021 raw15021Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw15021 raw15021Labels = mixedMoment B raw15021step0 raw15021step0Labels := by
      have hz : ∀ j, raw15021 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15021step0 = (fun i j => raw15021 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15021step0 raw15021; decide +kernel
      have hl : raw15021step0Labels = raw15021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15021 raw15021Labels permutation346 hz
    mixedMoment B raw15021step0 raw15021step0Labels = mixedMoment B raw15021step1 raw15021step1Labels := by
      have ha : raw15021step1 = (fun i j => raw15021step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15021step1 raw15021step0; decide +kernel
      have hl : raw15021step1Labels = raw15021step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15021step0 raw15021step0Labels permutation45 permutation6
    mixedMoment B raw15021step1 raw15021step1Labels = mixedMoment B raw15021step2 raw15021step2Labels := by
      have ha : raw15021step2 = -raw15021step1 := by apply Matrix.ext; change ∀ i j, raw15021step2 i j = -(raw15021step1 i j); unfold raw15021step2 raw15021step1; decide +kernel
      have hl : raw15021step2Labels = raw15021step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15021step2 raw15021step2Labels = mixedMoment B raw15021step3 raw15021step3Labels := by
      have ha : raw15021step3 = raw15021step2 := by apply Matrix.ext; unfold raw15021step3 raw15021step2; decide +kernel
      have hl : raw15021step2Labels = labelEmbedding9 ∘ raw15021step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15021step2 raw15021step2Labels raw15021step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw15022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15022step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15022 raw15022Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw15022 raw15022Labels = mixedMoment B raw15022step0 raw15022step0Labels := by
      have hz : ∀ j, raw15022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15022step0 = (fun i j => raw15022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15022step0 raw15022; decide +kernel
      have hl : raw15022step0Labels = raw15022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15022 raw15022Labels permutation346 hz
    mixedMoment B raw15022step0 raw15022step0Labels = mixedMoment B raw15022step1 raw15022step1Labels := by
      have hz : ∀ j, raw15022step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw15022step1 = (fun i j => raw15022step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw15022step1 raw15022step0; decide +kernel
      have hl : raw15022step1Labels = raw15022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15022step0 raw15022step0Labels permutation56 hz
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw15023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15023step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15023step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15023 raw15023Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw15023 raw15023Labels = mixedMoment B raw15023step0 raw15023step0Labels := by
      have ha : raw15023step0 = (fun i j => raw15023 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15023step0 raw15023; decide +kernel
      have hl : raw15023step0Labels = raw15023Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15023 raw15023Labels permutation271 permutation3
    mixedMoment B raw15023step0 raw15023step0Labels = mixedMoment B raw15023step1 raw15023step1Labels := by
      have ha : raw15023step1 = raw15023step0 := by apply Matrix.ext; unfold raw15023step1 raw15023step0; decide +kernel
      have hl : raw15023step0Labels = labelEmbedding6 ∘ raw15023step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15023step0 raw15023step0Labels raw15023step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw15024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw15024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15024 raw15024Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw15024 raw15024Labels = mixedMoment B raw15024step0 raw15024step0Labels := by
      have ha : raw15024step0 = (fun i j => raw15024 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15024step0 raw15024; decide +kernel
      have hl : raw15024step0Labels = raw15024Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15024 raw15024Labels permutation158 permutation2
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw15025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw15025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15025 raw15025Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw15025 raw15025Labels = mixedMoment B raw15025step0 raw15025step0Labels := by
      have hz : ∀ j, raw15025 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15025step0 = (fun i j => raw15025 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15025step0 raw15025; decide +kernel
      have hl : raw15025step0Labels = raw15025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15025 raw15025Labels permutation520 hz
    mixedMoment B raw15025step0 raw15025step0Labels = mixedMoment B raw15025step1 raw15025step1Labels := by
      have ha : raw15025step1 = (fun i j => raw15025step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15025step1 raw15025step0; decide +kernel
      have hl : raw15025step1Labels = raw15025step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15025step0 raw15025step0Labels permutation34 permutation2
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw15026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15026 raw15026Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw15026 raw15026Labels = mixedMoment B raw15026step0 raw15026step0Labels := by
      have ha : raw15026step0 = (fun i j => raw15026 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15026step0 raw15026; decide +kernel
      have hl : raw15026step0Labels = raw15026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15026 raw15026Labels permutation158 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw15027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15027step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15027 raw15027Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw15027 raw15027Labels = mixedMoment B raw15027step0 raw15027step0Labels := by
      have hz : ∀ j, raw15027 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15027step0 = (fun i j => raw15027 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15027step0 raw15027; decide +kernel
      have hl : raw15027step0Labels = raw15027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15027 raw15027Labels permutation346 hz
    mixedMoment B raw15027step0 raw15027step0Labels = mixedMoment B raw15027step1 raw15027step1Labels := by
      have ha : raw15027step1 = (fun i j => raw15027step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15027step1 raw15027step0; decide +kernel
      have hl : raw15027step1Labels = raw15027step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15027step0 raw15027step0Labels permutation34 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw15028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15028 raw15028Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw15028 raw15028Labels = mixedMoment B raw15028step0 raw15028step0Labels := by
      have ha : raw15028step0 = (fun i j => raw15028 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15028step0 raw15028; decide +kernel
      have hl : raw15028step0Labels = raw15028Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15028 raw15028Labels permutation154 permutation2
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw15029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15029 raw15029Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw15029 raw15029Labels = mixedMoment B raw15029step0 raw15029step0Labels := by
      have hz : ∀ j, raw15029 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15029step0 = (fun i j => raw15029 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15029step0 raw15029; decide +kernel
      have hl : raw15029step0Labels = raw15029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15029 raw15029Labels permutation520 hz
    mixedMoment B raw15029step0 raw15029step0Labels = mixedMoment B raw15029step1 raw15029step1Labels := by
      have hz : ∀ j, raw15029step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15029step1 = (fun i j => raw15029step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15029step1 raw15029step0; decide +kernel
      have hl : raw15029step1Labels = raw15029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15029step0 raw15029step0Labels permutation80 hz
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw15030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15030 raw15030Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw15030 raw15030Labels = mixedMoment B raw15030step0 raw15030step0Labels := by
      have hz : ∀ j, raw15030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15030step0 = (fun i j => raw15030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15030step0 raw15030; decide +kernel
      have hl : raw15030step0Labels = raw15030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15030 raw15030Labels permutation346 hz
    mixedMoment B raw15030step0 raw15030step0Labels = mixedMoment B raw15030step1 raw15030step1Labels := by
      have ha : raw15030step1 = (fun i j => raw15030step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15030step1 raw15030step0; decide +kernel
      have hl : raw15030step1Labels = raw15030step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15030step0 raw15030step0Labels permutation34 permutation2
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw15031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15031step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15031step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15031step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15031step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15031 raw15031Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw15031 raw15031Labels = mixedMoment B raw15031step0 raw15031step0Labels := by
      have hz : ∀ j, raw15031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15031step0 = (fun i j => raw15031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15031step0 raw15031; decide +kernel
      have hl : raw15031step0Labels = raw15031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15031 raw15031Labels permutation346 hz
    mixedMoment B raw15031step0 raw15031step0Labels = mixedMoment B raw15031step1 raw15031step1Labels := by
      have ha : raw15031step1 = (fun i j => raw15031step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15031step1 raw15031step0; decide +kernel
      have hl : raw15031step1Labels = raw15031step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15031step0 raw15031step0Labels permutation126 permutation3
    mixedMoment B raw15031step1 raw15031step1Labels = mixedMoment B raw15031step2 raw15031step2Labels := by
      have ha : raw15031step2 = -raw15031step1 := by apply Matrix.ext; change ∀ i j, raw15031step2 i j = -(raw15031step1 i j); unfold raw15031step2 raw15031step1; decide +kernel
      have hl : raw15031step2Labels = raw15031step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15031step2 raw15031step2Labels = mixedMoment B raw15031step3 raw15031step3Labels := by
      have ha : raw15031step3 = raw15031step2 := by apply Matrix.ext; unfold raw15031step3 raw15031step2; decide +kernel
      have hl : raw15031step2Labels = labelEmbedding6 ∘ raw15031step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15031step2 raw15031step2Labels raw15031step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw15032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15032step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15032step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15032step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15032step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15032 raw15032Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw15032 raw15032Labels = mixedMoment B raw15032step0 raw15032step0Labels := by
      have ha : raw15032step0 = (fun i j => raw15032 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15032step0 raw15032; decide +kernel
      have hl : raw15032step0Labels = raw15032Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15032 raw15032Labels permutation587 permutation3
    mixedMoment B raw15032step0 raw15032step0Labels = mixedMoment B raw15032step1 raw15032step1Labels := by
      have ha : raw15032step1 = -raw15032step0 := by apply Matrix.ext; change ∀ i j, raw15032step1 i j = -(raw15032step0 i j); unfold raw15032step1 raw15032step0; decide +kernel
      have hl : raw15032step1Labels = raw15032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15032step1 raw15032step1Labels = mixedMoment B raw15032step2 raw15032step2Labels := by
      have ha : raw15032step2 = raw15032step1 := by apply Matrix.ext; unfold raw15032step2 raw15032step1; decide +kernel
      have hl : raw15032step1Labels = labelEmbedding6 ∘ raw15032step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15032step1 raw15032step1Labels raw15032step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw15033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15033step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15033step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15033step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15033step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15033 raw15033Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw15033 raw15033Labels = mixedMoment B raw15033step0 raw15033step0Labels := by
      have hz : ∀ j, raw15033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15033step0 = (fun i j => raw15033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15033step0 raw15033; decide +kernel
      have hl : raw15033step0Labels = raw15033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15033 raw15033Labels permutation346 hz
    mixedMoment B raw15033step0 raw15033step0Labels = mixedMoment B raw15033step1 raw15033step1Labels := by
      have ha : raw15033step1 = (fun i j => raw15033step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15033step1 raw15033step0; decide +kernel
      have hl : raw15033step1Labels = raw15033step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15033step0 raw15033step0Labels permutation125 permutation3
    mixedMoment B raw15033step1 raw15033step1Labels = mixedMoment B raw15033step2 raw15033step2Labels := by
      have ha : raw15033step2 = -raw15033step1 := by apply Matrix.ext; change ∀ i j, raw15033step2 i j = -(raw15033step1 i j); unfold raw15033step2 raw15033step1; decide +kernel
      have hl : raw15033step2Labels = raw15033step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15033step2 raw15033step2Labels = mixedMoment B raw15033step3 raw15033step3Labels := by
      have ha : raw15033step3 = raw15033step2 := by apply Matrix.ext; unfold raw15033step3 raw15033step2; decide +kernel
      have hl : raw15033step2Labels = labelEmbedding6 ∘ raw15033step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15033step2 raw15033step2Labels raw15033step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw15034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw15034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw15034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15034 raw15034Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw15034 raw15034Labels = mixedMoment B raw15034step0 raw15034step0Labels := by
      have hz : ∀ j, raw15034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15034step0 = (fun i j => raw15034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15034step0 raw15034; decide +kernel
      have hl : raw15034step0Labels = raw15034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15034 raw15034Labels permutation346 hz
    mixedMoment B raw15034step0 raw15034step0Labels = mixedMoment B raw15034step1 raw15034step1Labels := by
      have ha : raw15034step1 = (fun i j => raw15034step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15034step1 raw15034step0; decide +kernel
      have hl : raw15034step1Labels = raw15034step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15034step0 raw15034step0Labels permutation33 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw15035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15035step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15035step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15035step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15035step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15035step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15035 raw15035Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw15035 raw15035Labels = mixedMoment B raw15035step0 raw15035step0Labels := by
      have hz : ∀ j, raw15035 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15035step0 = (fun i j => raw15035 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15035step0 raw15035; decide +kernel
      have hl : raw15035step0Labels = raw15035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15035 raw15035Labels permutation346 hz
    mixedMoment B raw15035step0 raw15035step0Labels = mixedMoment B raw15035step1 raw15035step1Labels := by
      have ha : raw15035step1 = (fun i j => raw15035step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15035step1 raw15035step0; decide +kernel
      have hl : raw15035step1Labels = raw15035step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15035step0 raw15035step0Labels permutation150 permutation3
    mixedMoment B raw15035step1 raw15035step1Labels = mixedMoment B raw15035step2 raw15035step2Labels := by
      have ha : raw15035step2 = -raw15035step1 := by apply Matrix.ext; change ∀ i j, raw15035step2 i j = -(raw15035step1 i j); unfold raw15035step2 raw15035step1; decide +kernel
      have hl : raw15035step2Labels = raw15035step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15035step2 raw15035step2Labels = mixedMoment B raw15035step3 raw15035step3Labels := by
      have ha : raw15035step3 = raw15035step2 := by apply Matrix.ext; unfold raw15035step3 raw15035step2; decide +kernel
      have hl : raw15035step2Labels = labelEmbedding6 ∘ raw15035step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15035step2 raw15035step2Labels raw15035step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw15036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15036step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15036step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15036step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15036 raw15036Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw15036 raw15036Labels = mixedMoment B raw15036step0 raw15036step0Labels := by
      have ha : raw15036step0 = (fun i j => raw15036 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15036step0 raw15036; decide +kernel
      have hl : raw15036step0Labels = raw15036Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15036 raw15036Labels permutation686 permutation3
    mixedMoment B raw15036step0 raw15036step0Labels = mixedMoment B raw15036step1 raw15036step1Labels := by
      have ha : raw15036step1 = -raw15036step0 := by apply Matrix.ext; change ∀ i j, raw15036step1 i j = -(raw15036step0 i j); unfold raw15036step1 raw15036step0; decide +kernel
      have hl : raw15036step1Labels = raw15036step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15036step1 raw15036step1Labels = mixedMoment B raw15036step2 raw15036step2Labels := by
      have ha : raw15036step2 = raw15036step1 := by apply Matrix.ext; unfold raw15036step2 raw15036step1; decide +kernel
      have hl : raw15036step1Labels = labelEmbedding6 ∘ raw15036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15036step1 raw15036step1Labels raw15036step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw15037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15037step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15037step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15037step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15037step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15037 raw15037Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw15037 raw15037Labels = mixedMoment B raw15037step0 raw15037step0Labels := by
      have hz : ∀ j, raw15037 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15037step0 = (fun i j => raw15037 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15037step0 raw15037; decide +kernel
      have hl : raw15037step0Labels = raw15037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15037 raw15037Labels permutation346 hz
    mixedMoment B raw15037step0 raw15037step0Labels = mixedMoment B raw15037step1 raw15037step1Labels := by
      have ha : raw15037step1 = (fun i j => raw15037step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15037step1 raw15037step0; decide +kernel
      have hl : raw15037step1Labels = raw15037step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15037step0 raw15037step0Labels permutation149 permutation3
    mixedMoment B raw15037step1 raw15037step1Labels = mixedMoment B raw15037step2 raw15037step2Labels := by
      have ha : raw15037step2 = -raw15037step1 := by apply Matrix.ext; change ∀ i j, raw15037step2 i j = -(raw15037step1 i j); unfold raw15037step2 raw15037step1; decide +kernel
      have hl : raw15037step2Labels = raw15037step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15037step2 raw15037step2Labels = mixedMoment B raw15037step3 raw15037step3Labels := by
      have ha : raw15037step3 = raw15037step2 := by apply Matrix.ext; unfold raw15037step3 raw15037step2; decide +kernel
      have hl : raw15037step2Labels = labelEmbedding6 ∘ raw15037step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15037step2 raw15037step2Labels raw15037step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw15038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw15038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw15038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw15038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15038step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15038step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15038step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15038step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15038 raw15038Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw15038 raw15038Labels = mixedMoment B raw15038step0 raw15038step0Labels := by
      have hz : ∀ j, raw15038 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15038step0 = (fun i j => raw15038 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15038step0 raw15038; decide +kernel
      have hl : raw15038step0Labels = raw15038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15038 raw15038Labels permutation520 hz
    mixedMoment B raw15038step0 raw15038step0Labels = mixedMoment B raw15038step1 raw15038step1Labels := by
      have hz : ∀ j, raw15038step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15038step1 = (fun i j => raw15038step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15038step1 raw15038step0; decide +kernel
      have hl : raw15038step1Labels = raw15038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15038step0 raw15038step0Labels permutation80 hz
    mixedMoment B raw15038step1 raw15038step1Labels = mixedMoment B raw15038step2 raw15038step2Labels := by
      have ha : raw15038step2 = (fun i j => raw15038step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15038step2 raw15038step1; decide +kernel
      have hl : raw15038step2Labels = raw15038step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15038step1 raw15038step1Labels permutation31 permutation3
    mixedMoment B raw15038step2 raw15038step2Labels = mixedMoment B raw15038step3 raw15038step3Labels := by
      have ha : raw15038step3 = -raw15038step2 := by apply Matrix.ext; change ∀ i j, raw15038step3 i j = -(raw15038step2 i j); unfold raw15038step3 raw15038step2; decide +kernel
      have hl : raw15038step3Labels = raw15038step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15038step3 raw15038step3Labels = mixedMoment B raw15038step4 raw15038step4Labels := by
      have ha : raw15038step4 = raw15038step3 := by apply Matrix.ext; unfold raw15038step4 raw15038step3; decide +kernel
      have hl : raw15038step3Labels = labelEmbedding6 ∘ raw15038step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15038step3 raw15038step3Labels raw15038step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw15039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15039step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15039 raw15039Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw15039 raw15039Labels = mixedMoment B raw15039step0 raw15039step0Labels := by
      have hz : ∀ j, raw15039 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15039step0 = (fun i j => raw15039 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15039step0 raw15039; decide +kernel
      have hl : raw15039step0Labels = raw15039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15039 raw15039Labels permutation346 hz
    mixedMoment B raw15039step0 raw15039step0Labels = mixedMoment B raw15039step1 raw15039step1Labels := by
      have ha : raw15039step1 = (fun i j => raw15039step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15039step1 raw15039step0; decide +kernel
      have hl : raw15039step1Labels = raw15039step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15039step0 raw15039step0Labels permutation56 permutation3
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw15040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15040 raw15040Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw15040 raw15040Labels = mixedMoment B raw15040step0 raw15040step0Labels := by
      have ha : raw15040step0 = (fun i j => raw15040 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15040step0 raw15040; decide +kernel
      have hl : raw15040step0Labels = raw15040Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15040 raw15040Labels permutation683 permutation3
    mixedMoment B raw15040step0 raw15040step0Labels = mixedMoment B raw15040step1 raw15040step1Labels := by
      have ha : raw15040step1 = -raw15040step0 := by apply Matrix.ext; change ∀ i j, raw15040step1 i j = -(raw15040step0 i j); unfold raw15040step1 raw15040step0; decide +kernel
      have hl : raw15040step1Labels = raw15040step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3979 node3979Labels := by rfl

def raw15041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15041step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15041step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15041 raw15041Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw15041 raw15041Labels = mixedMoment B raw15041step0 raw15041step0Labels := by
      have hz : ∀ j, raw15041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15041step0 = (fun i j => raw15041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15041step0 raw15041; decide +kernel
      have hl : raw15041step0Labels = raw15041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15041 raw15041Labels permutation346 hz
    mixedMoment B raw15041step0 raw15041step0Labels = mixedMoment B raw15041step1 raw15041step1Labels := by
      have ha : raw15041step1 = (fun i j => raw15041step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15041step1 raw15041step0; decide +kernel
      have hl : raw15041step1Labels = raw15041step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15041step0 raw15041step0Labels permutation146 permutation3
    mixedMoment B raw15041step1 raw15041step1Labels = mixedMoment B raw15041step2 raw15041step2Labels := by
      have ha : raw15041step2 = -raw15041step1 := by apply Matrix.ext; change ∀ i j, raw15041step2 i j = -(raw15041step1 i j); unfold raw15041step2 raw15041step1; decide +kernel
      have hl : raw15041step2Labels = raw15041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw15042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw15042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw15042step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15042step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw15042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15042step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw15042step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15042 raw15042Labels = mixedMoment B node4017 node4017Labels := by
  calc
    mixedMoment B raw15042 raw15042Labels = mixedMoment B raw15042step0 raw15042step0Labels := by
      have hz : ∀ j, raw15042 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15042step0 = (fun i j => raw15042 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15042step0 raw15042; decide +kernel
      have hl : raw15042step0Labels = raw15042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15042 raw15042Labels permutation520 hz
    mixedMoment B raw15042step0 raw15042step0Labels = mixedMoment B raw15042step1 raw15042step1Labels := by
      have hz : ∀ j, raw15042step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15042step1 = (fun i j => raw15042step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15042step1 raw15042step0; decide +kernel
      have hl : raw15042step1Labels = raw15042step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15042step0 raw15042step0Labels permutation80 hz
    mixedMoment B raw15042step1 raw15042step1Labels = mixedMoment B raw15042step2 raw15042step2Labels := by
      have ha : raw15042step2 = (fun i j => raw15042step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15042step2 raw15042step1; decide +kernel
      have hl : raw15042step2Labels = raw15042step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15042step1 raw15042step1Labels permutation30 permutation3
    mixedMoment B raw15042step2 raw15042step2Labels = mixedMoment B raw15042step3 raw15042step3Labels := by
      have ha : raw15042step3 = -raw15042step2 := by apply Matrix.ext; change ∀ i j, raw15042step3 i j = -(raw15042step2 i j); unfold raw15042step3 raw15042step2; decide +kernel
      have hl : raw15042step3Labels = raw15042step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4017 node4017Labels := by rfl

def raw15043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15043step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15043 raw15043Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw15043 raw15043Labels = mixedMoment B raw15043step0 raw15043step0Labels := by
      have hz : ∀ j, raw15043 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15043step0 = (fun i j => raw15043 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15043step0 raw15043; decide +kernel
      have hl : raw15043step0Labels = raw15043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15043 raw15043Labels permutation346 hz
    mixedMoment B raw15043step0 raw15043step0Labels = mixedMoment B raw15043step1 raw15043step1Labels := by
      have ha : raw15043step1 = (fun i j => raw15043step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15043step1 raw15043step0; decide +kernel
      have hl : raw15043step1Labels = raw15043step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15043step0 raw15043step0Labels permutation45 permutation6
    mixedMoment B raw15043step1 raw15043step1Labels = mixedMoment B raw15043step2 raw15043step2Labels := by
      have ha : raw15043step2 = -raw15043step1 := by apply Matrix.ext; change ∀ i j, raw15043step2 i j = -(raw15043step1 i j); unfold raw15043step2 raw15043step1; decide +kernel
      have hl : raw15043step2Labels = raw15043step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw15044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15044step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15044step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15044step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15044 raw15044Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw15044 raw15044Labels = mixedMoment B raw15044step0 raw15044step0Labels := by
      have hz : ∀ j, raw15044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15044step0 = (fun i j => raw15044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15044step0 raw15044; decide +kernel
      have hl : raw15044step0Labels = raw15044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15044 raw15044Labels permutation346 hz
    mixedMoment B raw15044step0 raw15044step0Labels = mixedMoment B raw15044step1 raw15044step1Labels := by
      have hz : ∀ j, raw15044step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw15044step1 = (fun i j => raw15044step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw15044step1 raw15044step0; decide +kernel
      have hl : raw15044step1Labels = raw15044step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15044step0 raw15044step0Labels permutation56 hz
    mixedMoment B raw15044step1 raw15044step1Labels = mixedMoment B raw15044step2 raw15044step2Labels := by
      have ha : raw15044step2 = (fun i j => raw15044step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15044step2 raw15044step1; decide +kernel
      have hl : raw15044step2Labels = raw15044step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15044step1 raw15044step1Labels permutation8 permutation3
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw15045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15045 raw15045Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw15045 raw15045Labels = mixedMoment B raw15045step0 raw15045step0Labels := by
      have ha : raw15045step0 = (fun i j => raw15045 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15045step0 raw15045; decide +kernel
      have hl : raw15045step0Labels = raw15045Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15045 raw15045Labels permutation271 permutation3
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw15046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15046 raw15046Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw15046 raw15046Labels = mixedMoment B raw15046step0 raw15046step0Labels := by
      have ha : raw15046step0 = (fun i j => raw15046 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15046step0 raw15046; decide +kernel
      have hl : raw15046step0Labels = raw15046Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15046 raw15046Labels permutation644 permutation3
    mixedMoment B raw15046step0 raw15046step0Labels = mixedMoment B raw15046step1 raw15046step1Labels := by
      have ha : raw15046step1 = -raw15046step0 := by apply Matrix.ext; change ∀ i j, raw15046step1 i j = -(raw15046step0 i j); unfold raw15046step1 raw15046step0; decide +kernel
      have hl : raw15046step1Labels = raw15046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

def raw15047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw15047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15047 raw15047Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw15047 raw15047Labels = mixedMoment B raw15047step0 raw15047step0Labels := by
      have hz : ∀ j, raw15047 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15047step0 = (fun i j => raw15047 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15047step0 raw15047; decide +kernel
      have hl : raw15047step0Labels = raw15047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15047 raw15047Labels permutation520 hz
    mixedMoment B raw15047step0 raw15047step0Labels = mixedMoment B raw15047step1 raw15047step1Labels := by
      have ha : raw15047step1 = (fun i j => raw15047step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15047step1 raw15047step0; decide +kernel
      have hl : raw15047step1Labels = raw15047step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15047step0 raw15047step0Labels permutation145 permutation3
    mixedMoment B raw15047step1 raw15047step1Labels = mixedMoment B raw15047step2 raw15047step2Labels := by
      have ha : raw15047step2 = -raw15047step1 := by apply Matrix.ext; change ∀ i j, raw15047step2 i j = -(raw15047step1 i j); unfold raw15047step2 raw15047step1; decide +kernel
      have hl : raw15047step2Labels = raw15047step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw15048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15048 raw15048Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw15048 raw15048Labels = mixedMoment B raw15048step0 raw15048step0Labels := by
      have ha : raw15048step0 = (fun i j => raw15048 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15048step0 raw15048; decide +kernel
      have hl : raw15048step0Labels = raw15048Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15048 raw15048Labels permutation162 permutation3
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw15049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15049Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15049step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15049 raw15049Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw15049 raw15049Labels = mixedMoment B raw15049step0 raw15049step0Labels := by
      have hz : ∀ j, raw15049 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15049step0 = (fun i j => raw15049 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15049step0 raw15049; decide +kernel
      have hl : raw15049step0Labels = raw15049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15049 raw15049Labels permutation346 hz
    mixedMoment B raw15049step0 raw15049step0Labels = mixedMoment B raw15049step1 raw15049step1Labels := by
      have ha : raw15049step1 = (fun i j => raw15049step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15049step1 raw15049step0; decide +kernel
      have hl : raw15049step1Labels = raw15049step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15049step0 raw15049step0Labels permutation56 permutation3
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw15050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15050 raw15050Labels = mixedMoment B node3967 node3967Labels := by
  calc
    mixedMoment B raw15050 raw15050Labels = mixedMoment B raw15050step0 raw15050step0Labels := by
      have ha : raw15050step0 = (fun i j => raw15050 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15050step0 raw15050; decide +kernel
      have hl : raw15050step0Labels = raw15050Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15050 raw15050Labels permutation686 permutation3
    mixedMoment B raw15050step0 raw15050step0Labels = mixedMoment B raw15050step1 raw15050step1Labels := by
      have ha : raw15050step1 = -raw15050step0 := by apply Matrix.ext; change ∀ i j, raw15050step1 i j = -(raw15050step0 i j); unfold raw15050step1 raw15050step0; decide +kernel
      have hl : raw15050step1Labels = raw15050step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3967 node3967Labels := by rfl

def raw15051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15051step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15051step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15051step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw15051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15051step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15051 raw15051Labels = mixedMoment B node4001 node4001Labels := by
  calc
    mixedMoment B raw15051 raw15051Labels = mixedMoment B raw15051step0 raw15051step0Labels := by
      have hz : ∀ j, raw15051 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15051step0 = (fun i j => raw15051 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15051step0 raw15051; decide +kernel
      have hl : raw15051step0Labels = raw15051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15051 raw15051Labels permutation520 hz
    mixedMoment B raw15051step0 raw15051step0Labels = mixedMoment B raw15051step1 raw15051step1Labels := by
      have hz : ∀ j, raw15051step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15051step1 = (fun i j => raw15051step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15051step1 raw15051step0; decide +kernel
      have hl : raw15051step1Labels = raw15051step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15051step0 raw15051step0Labels permutation80 hz
    mixedMoment B raw15051step1 raw15051step1Labels = mixedMoment B raw15051step2 raw15051step2Labels := by
      have ha : raw15051step2 = (fun i j => raw15051step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15051step2 raw15051step1; decide +kernel
      have hl : raw15051step2Labels = raw15051step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15051step1 raw15051step1Labels permutation31 permutation3
    mixedMoment B raw15051step2 raw15051step2Labels = mixedMoment B raw15051step3 raw15051step3Labels := by
      have ha : raw15051step3 = -raw15051step2 := by apply Matrix.ext; change ∀ i j, raw15051step3 i j = -(raw15051step2 i j); unfold raw15051step3 raw15051step2; decide +kernel
      have hl : raw15051step3Labels = raw15051step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4001 node4001Labels := by rfl

def raw15052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15052 raw15052Labels = mixedMoment B node4036 node4036Labels := by
  calc
    mixedMoment B raw15052 raw15052Labels = mixedMoment B raw15052step0 raw15052step0Labels := by
      have hz : ∀ j, raw15052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15052step0 = (fun i j => raw15052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15052step0 raw15052; decide +kernel
      have hl : raw15052step0Labels = raw15052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15052 raw15052Labels permutation346 hz
    mixedMoment B raw15052step0 raw15052step0Labels = mixedMoment B raw15052step1 raw15052step1Labels := by
      have ha : raw15052step1 = (fun i j => raw15052step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15052step1 raw15052step0; decide +kernel
      have hl : raw15052step1Labels = raw15052step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15052step0 raw15052step0Labels permutation33 permutation3
    _ = mixedMoment B node4036 node4036Labels := by rfl

def raw15053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15053step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15053step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15053 raw15053Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw15053 raw15053Labels = mixedMoment B raw15053step0 raw15053step0Labels := by
      have hz : ∀ j, raw15053 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15053step0 = (fun i j => raw15053 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15053step0 raw15053; decide +kernel
      have hl : raw15053step0Labels = raw15053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15053 raw15053Labels permutation346 hz
    mixedMoment B raw15053step0 raw15053step0Labels = mixedMoment B raw15053step1 raw15053step1Labels := by
      have ha : raw15053step1 = (fun i j => raw15053step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15053step1 raw15053step0; decide +kernel
      have hl : raw15053step1Labels = raw15053step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15053step0 raw15053step0Labels permutation126 permutation3
    mixedMoment B raw15053step1 raw15053step1Labels = mixedMoment B raw15053step2 raw15053step2Labels := by
      have ha : raw15053step2 = -raw15053step1 := by apply Matrix.ext; change ∀ i j, raw15053step2 i j = -(raw15053step1 i j); unfold raw15053step2 raw15053step1; decide +kernel
      have hl : raw15053step2Labels = raw15053step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw15054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15054 raw15054Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw15054 raw15054Labels = mixedMoment B raw15054step0 raw15054step0Labels := by
      have ha : raw15054step0 = (fun i j => raw15054 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15054step0 raw15054; decide +kernel
      have hl : raw15054step0Labels = raw15054Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15054 raw15054Labels permutation587 permutation3
    mixedMoment B raw15054step0 raw15054step0Labels = mixedMoment B raw15054step1 raw15054step1Labels := by
      have ha : raw15054step1 = -raw15054step0 := by apply Matrix.ext; change ∀ i j, raw15054step1 i j = -(raw15054step0 i j); unfold raw15054step1 raw15054step0; decide +kernel
      have hl : raw15054step1Labels = raw15054step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3692 node3692Labels := by rfl

def raw15055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15055 raw15055Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw15055 raw15055Labels = mixedMoment B raw15055step0 raw15055step0Labels := by
      have hz : ∀ j, raw15055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15055step0 = (fun i j => raw15055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15055step0 raw15055; decide +kernel
      have hl : raw15055step0Labels = raw15055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15055 raw15055Labels permutation346 hz
    mixedMoment B raw15055step0 raw15055step0Labels = mixedMoment B raw15055step1 raw15055step1Labels := by
      have ha : raw15055step1 = (fun i j => raw15055step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15055step1 raw15055step0; decide +kernel
      have hl : raw15055step1Labels = raw15055step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15055step0 raw15055step0Labels permutation125 permutation3
    mixedMoment B raw15055step1 raw15055step1Labels = mixedMoment B raw15055step2 raw15055step2Labels := by
      have ha : raw15055step2 = -raw15055step1 := by apply Matrix.ext; change ∀ i j, raw15055step2 i j = -(raw15055step1 i j); unfold raw15055step2 raw15055step1; decide +kernel
      have hl : raw15055step2Labels = raw15055step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw15056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw15056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw15056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15056 raw15056Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw15056 raw15056Labels = mixedMoment B raw15056step0 raw15056step0Labels := by
      have hz : ∀ j, raw15056 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15056step0 = (fun i j => raw15056 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15056step0 raw15056; decide +kernel
      have hl : raw15056step0Labels = raw15056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15056 raw15056Labels permutation346 hz
    mixedMoment B raw15056step0 raw15056step0Labels = mixedMoment B raw15056step1 raw15056step1Labels := by
      have ha : raw15056step1 = (fun i j => raw15056step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15056step1 raw15056step0; decide +kernel
      have hl : raw15056step1Labels = raw15056step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15056step0 raw15056step0Labels permutation127 permutation3
    mixedMoment B raw15056step1 raw15056step1Labels = mixedMoment B raw15056step2 raw15056step2Labels := by
      have ha : raw15056step2 = -raw15056step1 := by apply Matrix.ext; change ∀ i j, raw15056step2 i j = -(raw15056step1 i j); unfold raw15056step2 raw15056step1; decide +kernel
      have hl : raw15056step2Labels = raw15056step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw15057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15057 raw15057Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw15057 raw15057Labels = mixedMoment B raw15057step0 raw15057step0Labels := by
      have hz : ∀ j, raw15057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15057step0 = (fun i j => raw15057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15057step0 raw15057; decide +kernel
      have hl : raw15057step0Labels = raw15057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15057 raw15057Labels permutation346 hz
    mixedMoment B raw15057step0 raw15057step0Labels = mixedMoment B raw15057step1 raw15057step1Labels := by
      have ha : raw15057step1 = (fun i j => raw15057step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15057step1 raw15057step0; decide +kernel
      have hl : raw15057step1Labels = raw15057step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15057step0 raw15057step0Labels permutation150 permutation3
    mixedMoment B raw15057step1 raw15057step1Labels = mixedMoment B raw15057step2 raw15057step2Labels := by
      have ha : raw15057step2 = -raw15057step1 := by apply Matrix.ext; change ∀ i j, raw15057step2 i j = -(raw15057step1 i j); unfold raw15057step2 raw15057step1; decide +kernel
      have hl : raw15057step2Labels = raw15057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw15058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15058 raw15058Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw15058 raw15058Labels = mixedMoment B raw15058step0 raw15058step0Labels := by
      have ha : raw15058step0 = (fun i j => raw15058 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15058step0 raw15058; decide +kernel
      have hl : raw15058step0Labels = raw15058Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15058 raw15058Labels permutation686 permutation3
    mixedMoment B raw15058step0 raw15058step0Labels = mixedMoment B raw15058step1 raw15058step1Labels := by
      have ha : raw15058step1 = -raw15058step0 := by apply Matrix.ext; change ∀ i j, raw15058step1 i j = -(raw15058step0 i j); unfold raw15058step1 raw15058step0; decide +kernel
      have hl : raw15058step1Labels = raw15058step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw15059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15059 raw15059Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw15059 raw15059Labels = mixedMoment B raw15059step0 raw15059step0Labels := by
      have hz : ∀ j, raw15059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15059step0 = (fun i j => raw15059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15059step0 raw15059; decide +kernel
      have hl : raw15059step0Labels = raw15059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15059 raw15059Labels permutation346 hz
    mixedMoment B raw15059step0 raw15059step0Labels = mixedMoment B raw15059step1 raw15059step1Labels := by
      have ha : raw15059step1 = (fun i j => raw15059step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15059step1 raw15059step0; decide +kernel
      have hl : raw15059step1Labels = raw15059step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15059step0 raw15059step0Labels permutation149 permutation3
    mixedMoment B raw15059step1 raw15059step1Labels = mixedMoment B raw15059step2 raw15059step2Labels := by
      have ha : raw15059step2 = -raw15059step1 := by apply Matrix.ext; change ∀ i j, raw15059step2 i j = -(raw15059step1 i j); unfold raw15059step2 raw15059step1; decide +kernel
      have hl : raw15059step2Labels = raw15059step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw15060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw15060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw15060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15060step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw15060step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15060step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15060step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15060step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15060 raw15060Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw15060 raw15060Labels = mixedMoment B raw15060step0 raw15060step0Labels := by
      have hz : ∀ j, raw15060 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15060step0 = (fun i j => raw15060 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15060step0 raw15060; decide +kernel
      have hl : raw15060step0Labels = raw15060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15060 raw15060Labels permutation520 hz
    mixedMoment B raw15060step0 raw15060step0Labels = mixedMoment B raw15060step1 raw15060step1Labels := by
      have hz : ∀ j, raw15060step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15060step1 = (fun i j => raw15060step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15060step1 raw15060step0; decide +kernel
      have hl : raw15060step1Labels = raw15060step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15060step0 raw15060step0Labels permutation80 hz
    mixedMoment B raw15060step1 raw15060step1Labels = mixedMoment B raw15060step2 raw15060step2Labels := by
      have ha : raw15060step2 = (fun i j => raw15060step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15060step2 raw15060step1; decide +kernel
      have hl : raw15060step2Labels = raw15060step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15060step1 raw15060step1Labels permutation31 permutation3
    mixedMoment B raw15060step2 raw15060step2Labels = mixedMoment B raw15060step3 raw15060step3Labels := by
      have ha : raw15060step3 = -raw15060step2 := by apply Matrix.ext; change ∀ i j, raw15060step3 i j = -(raw15060step2 i j); unfold raw15060step3 raw15060step2; decide +kernel
      have hl : raw15060step3Labels = raw15060step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw15061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15061step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15061step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15061 raw15061Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw15061 raw15061Labels = mixedMoment B raw15061step0 raw15061step0Labels := by
      have hz : ∀ j, raw15061 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15061step0 = (fun i j => raw15061 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15061step0 raw15061; decide +kernel
      have hl : raw15061step0Labels = raw15061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15061 raw15061Labels permutation346 hz
    mixedMoment B raw15061step0 raw15061step0Labels = mixedMoment B raw15061step1 raw15061step1Labels := by
      have ha : raw15061step1 = (fun i j => raw15061step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15061step1 raw15061step0; decide +kernel
      have hl : raw15061step1Labels = raw15061step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15061step0 raw15061step0Labels permutation126 permutation2
    mixedMoment B raw15061step1 raw15061step1Labels = mixedMoment B raw15061step2 raw15061step2Labels := by
      have ha : raw15061step2 = -raw15061step1 := by apply Matrix.ext; change ∀ i j, raw15061step2 i j = -(raw15061step1 i j); unfold raw15061step2 raw15061step1; decide +kernel
      have hl : raw15061step2Labels = raw15061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw15062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15062step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15062step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15062 raw15062Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw15062 raw15062Labels = mixedMoment B raw15062step0 raw15062step0Labels := by
      have hz : ∀ j, raw15062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15062step0 = (fun i j => raw15062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15062step0 raw15062; decide +kernel
      have hl : raw15062step0Labels = raw15062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15062 raw15062Labels permutation346 hz
    mixedMoment B raw15062step0 raw15062step0Labels = mixedMoment B raw15062step1 raw15062step1Labels := by
      have ha : raw15062step1 = (fun i j => raw15062step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15062step1 raw15062step0; decide +kernel
      have hl : raw15062step1Labels = raw15062step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15062step0 raw15062step0Labels permutation32 permutation3
    mixedMoment B raw15062step1 raw15062step1Labels = mixedMoment B raw15062step2 raw15062step2Labels := by
      have ha : raw15062step2 = raw15062step1 := by apply Matrix.ext; unfold raw15062step2 raw15062step1; decide +kernel
      have hl : raw15062step1Labels = labelEmbedding6 ∘ raw15062step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15062step1 raw15062step1Labels raw15062step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw15063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15063step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15063 raw15063Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw15063 raw15063Labels = mixedMoment B raw15063step0 raw15063step0Labels := by
      have ha : raw15063step0 = (fun i j => raw15063 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15063step0 raw15063; decide +kernel
      have hl : raw15063step0Labels = raw15063Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15063 raw15063Labels permutation176 permutation3
    mixedMoment B raw15063step0 raw15063step0Labels = mixedMoment B raw15063step1 raw15063step1Labels := by
      have ha : raw15063step1 = raw15063step0 := by apply Matrix.ext; unfold raw15063step1 raw15063step0; decide +kernel
      have hl : raw15063step0Labels = labelEmbedding6 ∘ raw15063step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15063step0 raw15063step0Labels raw15063step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw15064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15064step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15064step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15064 raw15064Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw15064 raw15064Labels = mixedMoment B raw15064step0 raw15064step0Labels := by
      have hz : ∀ j, raw15064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15064step0 = (fun i j => raw15064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15064step0 raw15064; decide +kernel
      have hl : raw15064step0Labels = raw15064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15064 raw15064Labels permutation346 hz
    mixedMoment B raw15064step0 raw15064step0Labels = mixedMoment B raw15064step1 raw15064step1Labels := by
      have ha : raw15064step1 = (fun i j => raw15064step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15064step1 raw15064step0; decide +kernel
      have hl : raw15064step1Labels = raw15064step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15064step0 raw15064step0Labels permutation38 permutation3
    mixedMoment B raw15064step1 raw15064step1Labels = mixedMoment B raw15064step2 raw15064step2Labels := by
      have ha : raw15064step2 = raw15064step1 := by apply Matrix.ext; unfold raw15064step2 raw15064step1; decide +kernel
      have hl : raw15064step1Labels = labelEmbedding6 ∘ raw15064step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15064step1 raw15064step1Labels raw15064step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw15065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15065step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15065step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15065step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15065step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15065step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15065 raw15065Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw15065 raw15065Labels = mixedMoment B raw15065step0 raw15065step0Labels := by
      have hz : ∀ j, raw15065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15065step0 = (fun i j => raw15065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15065step0 raw15065; decide +kernel
      have hl : raw15065step0Labels = raw15065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15065 raw15065Labels permutation346 hz
    mixedMoment B raw15065step0 raw15065step0Labels = mixedMoment B raw15065step1 raw15065step1Labels := by
      have ha : raw15065step1 = (fun i j => raw15065step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15065step1 raw15065step0; decide +kernel
      have hl : raw15065step1Labels = raw15065step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15065step0 raw15065step0Labels permutation44 permutation5
    mixedMoment B raw15065step1 raw15065step1Labels = mixedMoment B raw15065step2 raw15065step2Labels := by
      have ha : raw15065step2 = -raw15065step1 := by apply Matrix.ext; change ∀ i j, raw15065step2 i j = -(raw15065step1 i j); unfold raw15065step2 raw15065step1; decide +kernel
      have hl : raw15065step2Labels = raw15065step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15065step2 raw15065step2Labels = mixedMoment B raw15065step3 raw15065step3Labels := by
      have ha : raw15065step3 = raw15065step2 := by apply Matrix.ext; unfold raw15065step3 raw15065step2; decide +kernel
      have hl : raw15065step2Labels = labelEmbedding8 ∘ raw15065step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15065step2 raw15065step2Labels raw15065step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw15066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15066step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15066step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15066 raw15066Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw15066 raw15066Labels = mixedMoment B raw15066step0 raw15066step0Labels := by
      have ha : raw15066step0 = (fun i j => raw15066 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15066step0 raw15066; decide +kernel
      have hl : raw15066step0Labels = raw15066Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15066 raw15066Labels permutation160 permutation3
    mixedMoment B raw15066step0 raw15066step0Labels = mixedMoment B raw15066step1 raw15066step1Labels := by
      have ha : raw15066step1 = raw15066step0 := by apply Matrix.ext; unfold raw15066step1 raw15066step0; decide +kernel
      have hl : raw15066step0Labels = labelEmbedding6 ∘ raw15066step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15066step0 raw15066step0Labels raw15066step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw15067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15067step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15067 raw15067Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw15067 raw15067Labels = mixedMoment B raw15067step0 raw15067step0Labels := by
      have ha : raw15067step0 = (fun i j => raw15067 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15067step0 raw15067; decide +kernel
      have hl : raw15067step0Labels = raw15067Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15067 raw15067Labels permutation160 permutation3
    mixedMoment B raw15067step0 raw15067step0Labels = mixedMoment B raw15067step1 raw15067step1Labels := by
      have ha : raw15067step1 = raw15067step0 := by apply Matrix.ext; unfold raw15067step1 raw15067step0; decide +kernel
      have hl : raw15067step0Labels = labelEmbedding6 ∘ raw15067step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15067step0 raw15067step0Labels raw15067step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw15068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15068step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15068 raw15068Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw15068 raw15068Labels = mixedMoment B raw15068step0 raw15068step0Labels := by
      have ha : raw15068step0 = (fun i j => raw15068 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15068step0 raw15068; decide +kernel
      have hl : raw15068step0Labels = raw15068Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15068 raw15068Labels permutation160 permutation3
    mixedMoment B raw15068step0 raw15068step0Labels = mixedMoment B raw15068step1 raw15068step1Labels := by
      have ha : raw15068step1 = raw15068step0 := by apply Matrix.ext; unfold raw15068step1 raw15068step0; decide +kernel
      have hl : raw15068step0Labels = labelEmbedding6 ∘ raw15068step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15068step0 raw15068step0Labels raw15068step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw15069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15069step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15069 raw15069Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw15069 raw15069Labels = mixedMoment B raw15069step0 raw15069step0Labels := by
      have ha : raw15069step0 = (fun i j => raw15069 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15069step0 raw15069; decide +kernel
      have hl : raw15069step0Labels = raw15069Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15069 raw15069Labels permutation166 permutation3
    mixedMoment B raw15069step0 raw15069step0Labels = mixedMoment B raw15069step1 raw15069step1Labels := by
      have ha : raw15069step1 = raw15069step0 := by apply Matrix.ext; unfold raw15069step1 raw15069step0; decide +kernel
      have hl : raw15069step0Labels = labelEmbedding6 ∘ raw15069step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15069step0 raw15069step0Labels raw15069step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw15070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15070step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15070 raw15070Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw15070 raw15070Labels = mixedMoment B raw15070step0 raw15070step0Labels := by
      have hz : ∀ j, raw15070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15070step0 = (fun i j => raw15070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15070step0 raw15070; decide +kernel
      have hl : raw15070step0Labels = raw15070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15070 raw15070Labels permutation346 hz
    mixedMoment B raw15070step0 raw15070step0Labels = mixedMoment B raw15070step1 raw15070step1Labels := by
      have ha : raw15070step1 = (fun i j => raw15070step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15070step1 raw15070step0; decide +kernel
      have hl : raw15070step1Labels = raw15070step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15070step0 raw15070step0Labels permutation34 permutation3
    mixedMoment B raw15070step1 raw15070step1Labels = mixedMoment B raw15070step2 raw15070step2Labels := by
      have ha : raw15070step2 = raw15070step1 := by apply Matrix.ext; unfold raw15070step2 raw15070step1; decide +kernel
      have hl : raw15070step1Labels = labelEmbedding6 ∘ raw15070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15070step1 raw15070step1Labels raw15070step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw15071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15071step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15071step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15071 raw15071Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw15071 raw15071Labels = mixedMoment B raw15071step0 raw15071step0Labels := by
      have hz : ∀ j, raw15071 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15071step0 = (fun i j => raw15071 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15071step0 raw15071; decide +kernel
      have hl : raw15071step0Labels = raw15071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15071 raw15071Labels permutation346 hz
    mixedMoment B raw15071step0 raw15071step0Labels = mixedMoment B raw15071step1 raw15071step1Labels := by
      have ha : raw15071step1 = (fun i j => raw15071step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15071step1 raw15071step0; decide +kernel
      have hl : raw15071step1Labels = raw15071step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15071step0 raw15071step0Labels permutation34 permutation3
    mixedMoment B raw15071step1 raw15071step1Labels = mixedMoment B raw15071step2 raw15071step2Labels := by
      have ha : raw15071step2 = raw15071step1 := by apply Matrix.ext; unfold raw15071step2 raw15071step1; decide +kernel
      have hl : raw15071step1Labels = labelEmbedding6 ∘ raw15071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15071step1 raw15071step1Labels raw15071step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw15072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15072step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15072 raw15072Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw15072 raw15072Labels = mixedMoment B raw15072step0 raw15072step0Labels := by
      have ha : raw15072step0 = (fun i j => raw15072 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15072step0 raw15072; decide +kernel
      have hl : raw15072step0Labels = raw15072Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15072 raw15072Labels permutation178 permutation3
    mixedMoment B raw15072step0 raw15072step0Labels = mixedMoment B raw15072step1 raw15072step1Labels := by
      have ha : raw15072step1 = raw15072step0 := by apply Matrix.ext; unfold raw15072step1 raw15072step0; decide +kernel
      have hl : raw15072step0Labels = labelEmbedding6 ∘ raw15072step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15072step0 raw15072step0Labels raw15072step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw15073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15073step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15073step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15073 raw15073Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw15073 raw15073Labels = mixedMoment B raw15073step0 raw15073step0Labels := by
      have hz : ∀ j, raw15073 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15073step0 = (fun i j => raw15073 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15073step0 raw15073; decide +kernel
      have hl : raw15073step0Labels = raw15073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15073 raw15073Labels permutation346 hz
    mixedMoment B raw15073step0 raw15073step0Labels = mixedMoment B raw15073step1 raw15073step1Labels := by
      have ha : raw15073step1 = (fun i j => raw15073step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15073step1 raw15073step0; decide +kernel
      have hl : raw15073step1Labels = raw15073step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15073step0 raw15073step0Labels permutation34 permutation3
    mixedMoment B raw15073step1 raw15073step1Labels = mixedMoment B raw15073step2 raw15073step2Labels := by
      have ha : raw15073step2 = raw15073step1 := by apply Matrix.ext; unfold raw15073step2 raw15073step1; decide +kernel
      have hl : raw15073step1Labels = labelEmbedding6 ∘ raw15073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15073step1 raw15073step1Labels raw15073step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw15074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15074step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15074step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15074 raw15074Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw15074 raw15074Labels = mixedMoment B raw15074step0 raw15074step0Labels := by
      have hz : ∀ j, raw15074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15074step0 = (fun i j => raw15074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15074step0 raw15074; decide +kernel
      have hl : raw15074step0Labels = raw15074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15074 raw15074Labels permutation346 hz
    mixedMoment B raw15074step0 raw15074step0Labels = mixedMoment B raw15074step1 raw15074step1Labels := by
      have ha : raw15074step1 = (fun i j => raw15074step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15074step1 raw15074step0; decide +kernel
      have hl : raw15074step1Labels = raw15074step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15074step0 raw15074step0Labels permutation32 permutation3
    mixedMoment B raw15074step1 raw15074step1Labels = mixedMoment B raw15074step2 raw15074step2Labels := by
      have ha : raw15074step2 = raw15074step1 := by apply Matrix.ext; unfold raw15074step2 raw15074step1; decide +kernel
      have hl : raw15074step1Labels = labelEmbedding6 ∘ raw15074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15074step1 raw15074step1Labels raw15074step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw15075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15075step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15075step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15075 raw15075Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw15075 raw15075Labels = mixedMoment B raw15075step0 raw15075step0Labels := by
      have hz : ∀ j, raw15075 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15075step0 = (fun i j => raw15075 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15075step0 raw15075; decide +kernel
      have hl : raw15075step0Labels = raw15075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15075 raw15075Labels permutation346 hz
    mixedMoment B raw15075step0 raw15075step0Labels = mixedMoment B raw15075step1 raw15075step1Labels := by
      have ha : raw15075step1 = (fun i j => raw15075step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15075step1 raw15075step0; decide +kernel
      have hl : raw15075step1Labels = raw15075step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15075step0 raw15075step0Labels permutation32 permutation3
    mixedMoment B raw15075step1 raw15075step1Labels = mixedMoment B raw15075step2 raw15075step2Labels := by
      have ha : raw15075step2 = raw15075step1 := by apply Matrix.ext; unfold raw15075step2 raw15075step1; decide +kernel
      have hl : raw15075step1Labels = labelEmbedding6 ∘ raw15075step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15075step1 raw15075step1Labels raw15075step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw15076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15076step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15076 raw15076Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw15076 raw15076Labels = mixedMoment B raw15076step0 raw15076step0Labels := by
      have ha : raw15076step0 = (fun i j => raw15076 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15076step0 raw15076; decide +kernel
      have hl : raw15076step0Labels = raw15076Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15076 raw15076Labels permutation176 permutation3
    mixedMoment B raw15076step0 raw15076step0Labels = mixedMoment B raw15076step1 raw15076step1Labels := by
      have ha : raw15076step1 = raw15076step0 := by apply Matrix.ext; unfold raw15076step1 raw15076step0; decide +kernel
      have hl : raw15076step0Labels = labelEmbedding6 ∘ raw15076step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15076step0 raw15076step0Labels raw15076step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw15077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw15077step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw15077step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15077 raw15077Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw15077 raw15077Labels = mixedMoment B raw15077step0 raw15077step0Labels := by
      have hz : ∀ j, raw15077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15077step0 = (fun i j => raw15077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15077step0 raw15077; decide +kernel
      have hl : raw15077step0Labels = raw15077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15077 raw15077Labels permutation346 hz
    mixedMoment B raw15077step0 raw15077step0Labels = mixedMoment B raw15077step1 raw15077step1Labels := by
      have ha : raw15077step1 = (fun i j => raw15077step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15077step1 raw15077step0; decide +kernel
      have hl : raw15077step1Labels = raw15077step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15077step0 raw15077step0Labels permutation32 permutation3
    mixedMoment B raw15077step1 raw15077step1Labels = mixedMoment B raw15077step2 raw15077step2Labels := by
      have ha : raw15077step2 = raw15077step1 := by apply Matrix.ext; unfold raw15077step2 raw15077step1; decide +kernel
      have hl : raw15077step1Labels = labelEmbedding6 ∘ raw15077step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15077step1 raw15077step1Labels raw15077step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw15078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw15078step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw15078step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15078 raw15078Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw15078 raw15078Labels = mixedMoment B raw15078step0 raw15078step0Labels := by
      have hz : ∀ j, raw15078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15078step0 = (fun i j => raw15078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15078step0 raw15078; decide +kernel
      have hl : raw15078step0Labels = raw15078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15078 raw15078Labels permutation346 hz
    mixedMoment B raw15078step0 raw15078step0Labels = mixedMoment B raw15078step1 raw15078step1Labels := by
      have ha : raw15078step1 = (fun i j => raw15078step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15078step1 raw15078step0; decide +kernel
      have hl : raw15078step1Labels = raw15078step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15078step0 raw15078step0Labels permutation32 permutation3
    mixedMoment B raw15078step1 raw15078step1Labels = mixedMoment B raw15078step2 raw15078step2Labels := by
      have ha : raw15078step2 = raw15078step1 := by apply Matrix.ext; unfold raw15078step2 raw15078step1; decide +kernel
      have hl : raw15078step1Labels = labelEmbedding6 ∘ raw15078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15078step1 raw15078step1Labels raw15078step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw15079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw15079step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15079step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15079step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15079step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15079 raw15079Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw15079 raw15079Labels = mixedMoment B raw15079step0 raw15079step0Labels := by
      have hz : ∀ j, raw15079 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15079step0 = (fun i j => raw15079 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15079step0 raw15079; decide +kernel
      have hl : raw15079step0Labels = raw15079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15079 raw15079Labels permutation346 hz
    mixedMoment B raw15079step0 raw15079step0Labels = mixedMoment B raw15079step1 raw15079step1Labels := by
      have ha : raw15079step1 = (fun i j => raw15079step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15079step1 raw15079step0; decide +kernel
      have hl : raw15079step1Labels = raw15079step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15079step0 raw15079step0Labels permutation151 permutation3
    mixedMoment B raw15079step1 raw15079step1Labels = mixedMoment B raw15079step2 raw15079step2Labels := by
      have ha : raw15079step2 = -raw15079step1 := by apply Matrix.ext; change ∀ i j, raw15079step2 i j = -(raw15079step1 i j); unfold raw15079step2 raw15079step1; decide +kernel
      have hl : raw15079step2Labels = raw15079step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15079step2 raw15079step2Labels = mixedMoment B raw15079step3 raw15079step3Labels := by
      have ha : raw15079step3 = raw15079step2 := by apply Matrix.ext; unfold raw15079step3 raw15079step2; decide +kernel
      have hl : raw15079step2Labels = labelEmbedding6 ∘ raw15079step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15079step2 raw15079step2Labels raw15079step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw15080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15080step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15080step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15080step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15080step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15080 raw15080Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw15080 raw15080Labels = mixedMoment B raw15080step0 raw15080step0Labels := by
      have ha : raw15080step0 = (fun i j => raw15080 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15080step0 raw15080; decide +kernel
      have hl : raw15080step0Labels = raw15080Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15080 raw15080Labels permutation686 permutation3
    mixedMoment B raw15080step0 raw15080step0Labels = mixedMoment B raw15080step1 raw15080step1Labels := by
      have ha : raw15080step1 = -raw15080step0 := by apply Matrix.ext; change ∀ i j, raw15080step1 i j = -(raw15080step0 i j); unfold raw15080step1 raw15080step0; decide +kernel
      have hl : raw15080step1Labels = raw15080step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15080step1 raw15080step1Labels = mixedMoment B raw15080step2 raw15080step2Labels := by
      have ha : raw15080step2 = raw15080step1 := by apply Matrix.ext; unfold raw15080step2 raw15080step1; decide +kernel
      have hl : raw15080step1Labels = labelEmbedding6 ∘ raw15080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15080step1 raw15080step1Labels raw15080step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw15081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15081step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15081step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15081step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15081step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15081 raw15081Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw15081 raw15081Labels = mixedMoment B raw15081step0 raw15081step0Labels := by
      have hz : ∀ j, raw15081 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15081step0 = (fun i j => raw15081 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15081step0 raw15081; decide +kernel
      have hl : raw15081step0Labels = raw15081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15081 raw15081Labels permutation346 hz
    mixedMoment B raw15081step0 raw15081step0Labels = mixedMoment B raw15081step1 raw15081step1Labels := by
      have ha : raw15081step1 = (fun i j => raw15081step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15081step1 raw15081step0; decide +kernel
      have hl : raw15081step1Labels = raw15081step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15081step0 raw15081step0Labels permutation149 permutation3
    mixedMoment B raw15081step1 raw15081step1Labels = mixedMoment B raw15081step2 raw15081step2Labels := by
      have ha : raw15081step2 = -raw15081step1 := by apply Matrix.ext; change ∀ i j, raw15081step2 i j = -(raw15081step1 i j); unfold raw15081step2 raw15081step1; decide +kernel
      have hl : raw15081step2Labels = raw15081step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15081step2 raw15081step2Labels = mixedMoment B raw15081step3 raw15081step3Labels := by
      have ha : raw15081step3 = raw15081step2 := by apply Matrix.ext; unfold raw15081step3 raw15081step2; decide +kernel
      have hl : raw15081step2Labels = labelEmbedding6 ∘ raw15081step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15081step2 raw15081step2Labels raw15081step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw15082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw15082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw15082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15082step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15082step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15082step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15082step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15082 raw15082Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw15082 raw15082Labels = mixedMoment B raw15082step0 raw15082step0Labels := by
      have hz : ∀ j, raw15082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15082step0 = (fun i j => raw15082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15082step0 raw15082; decide +kernel
      have hl : raw15082step0Labels = raw15082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15082 raw15082Labels permutation346 hz
    mixedMoment B raw15082step0 raw15082step0Labels = mixedMoment B raw15082step1 raw15082step1Labels := by
      have ha : raw15082step1 = (fun i j => raw15082step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15082step1 raw15082step0; decide +kernel
      have hl : raw15082step1Labels = raw15082step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15082step0 raw15082step0Labels permutation145 permutation3
    mixedMoment B raw15082step1 raw15082step1Labels = mixedMoment B raw15082step2 raw15082step2Labels := by
      have ha : raw15082step2 = -raw15082step1 := by apply Matrix.ext; change ∀ i j, raw15082step2 i j = -(raw15082step1 i j); unfold raw15082step2 raw15082step1; decide +kernel
      have hl : raw15082step2Labels = raw15082step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15082step2 raw15082step2Labels = mixedMoment B raw15082step3 raw15082step3Labels := by
      have ha : raw15082step3 = raw15082step2 := by apply Matrix.ext; unfold raw15082step3 raw15082step2; decide +kernel
      have hl : raw15082step2Labels = labelEmbedding6 ∘ raw15082step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15082step2 raw15082step2Labels raw15082step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw15083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15083step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15083 raw15083Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw15083 raw15083Labels = mixedMoment B raw15083step0 raw15083step0Labels := by
      have hz : ∀ j, raw15083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15083step0 = (fun i j => raw15083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15083step0 raw15083; decide +kernel
      have hl : raw15083step0Labels = raw15083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15083 raw15083Labels permutation346 hz
    mixedMoment B raw15083step0 raw15083step0Labels = mixedMoment B raw15083step1 raw15083step1Labels := by
      have ha : raw15083step1 = (fun i j => raw15083step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15083step1 raw15083step0; decide +kernel
      have hl : raw15083step1Labels = raw15083step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15083step0 raw15083step0Labels permutation56 permutation3
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw15084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15084 raw15084Labels = mixedMoment B node3992 node3992Labels := by
  calc
    mixedMoment B raw15084 raw15084Labels = mixedMoment B raw15084step0 raw15084step0Labels := by
      have ha : raw15084step0 = (fun i j => raw15084 (permutation685 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15084step0 raw15084; decide +kernel
      have hl : raw15084step0Labels = raw15084Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15084 raw15084Labels permutation685 permutation3
    mixedMoment B raw15084step0 raw15084step0Labels = mixedMoment B raw15084step1 raw15084step1Labels := by
      have ha : raw15084step1 = -raw15084step0 := by apply Matrix.ext; change ∀ i j, raw15084step1 i j = -(raw15084step0 i j); unfold raw15084step1 raw15084step0; decide +kernel
      have hl : raw15084step1Labels = raw15084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3992 node3992Labels := by rfl

def raw15085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15085Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15085step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15085 raw15085Labels = mixedMoment B node3999 node3999Labels := by
  calc
    mixedMoment B raw15085 raw15085Labels = mixedMoment B raw15085step0 raw15085step0Labels := by
      have hz : ∀ j, raw15085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15085step0 = (fun i j => raw15085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15085step0 raw15085; decide +kernel
      have hl : raw15085step0Labels = raw15085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15085 raw15085Labels permutation346 hz
    mixedMoment B raw15085step0 raw15085step0Labels = mixedMoment B raw15085step1 raw15085step1Labels := by
      have ha : raw15085step1 = (fun i j => raw15085step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15085step1 raw15085step0; decide +kernel
      have hl : raw15085step1Labels = raw15085step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15085step0 raw15085step0Labels permutation149 permutation3
    mixedMoment B raw15085step1 raw15085step1Labels = mixedMoment B raw15085step2 raw15085step2Labels := by
      have ha : raw15085step2 = -raw15085step1 := by apply Matrix.ext; change ∀ i j, raw15085step2 i j = -(raw15085step1 i j); unfold raw15085step2 raw15085step1; decide +kernel
      have hl : raw15085step2Labels = raw15085step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3999 node3999Labels := by rfl

def raw15086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15086Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15086step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15086 raw15086Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw15086 raw15086Labels = mixedMoment B raw15086step0 raw15086step0Labels := by
      have hz : ∀ j, raw15086 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15086step0 = (fun i j => raw15086 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15086step0 raw15086; decide +kernel
      have hl : raw15086step0Labels = raw15086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15086 raw15086Labels permutation346 hz
    mixedMoment B raw15086step0 raw15086step0Labels = mixedMoment B raw15086step1 raw15086step1Labels := by
      have ha : raw15086step1 = (fun i j => raw15086step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15086step1 raw15086step0; decide +kernel
      have hl : raw15086step1Labels = raw15086step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15086step0 raw15086step0Labels permutation145 permutation3
    mixedMoment B raw15086step1 raw15086step1Labels = mixedMoment B raw15086step2 raw15086step2Labels := by
      have ha : raw15086step2 = -raw15086step1 := by apply Matrix.ext; change ∀ i j, raw15086step2 i j = -(raw15086step1 i j); unfold raw15086step2 raw15086step1; decide +kernel
      have hl : raw15086step2Labels = raw15086step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw15087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15087Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15087step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw15087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15087 raw15087Labels = mixedMoment B node4054 node4054Labels := by
  calc
    mixedMoment B raw15087 raw15087Labels = mixedMoment B raw15087step0 raw15087step0Labels := by
      have hz : ∀ j, raw15087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15087step0 = (fun i j => raw15087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15087step0 raw15087; decide +kernel
      have hl : raw15087step0Labels = raw15087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15087 raw15087Labels permutation346 hz
    mixedMoment B raw15087step0 raw15087step0Labels = mixedMoment B raw15087step1 raw15087step1Labels := by
      have ha : raw15087step1 = (fun i j => raw15087step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15087step1 raw15087step0; decide +kernel
      have hl : raw15087step1Labels = raw15087step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15087step0 raw15087step0Labels permutation32 permutation3
    _ = mixedMoment B node4054 node4054Labels := by rfl

def raw15088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15088Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15088step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15088 raw15088Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw15088 raw15088Labels = mixedMoment B raw15088step0 raw15088step0Labels := by
      have hz : ∀ j, raw15088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15088step0 = (fun i j => raw15088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15088step0 raw15088; decide +kernel
      have hl : raw15088step0Labels = raw15088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15088 raw15088Labels permutation346 hz
    mixedMoment B raw15088step0 raw15088step0Labels = mixedMoment B raw15088step1 raw15088step1Labels := by
      have ha : raw15088step1 = (fun i j => raw15088step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15088step1 raw15088step0; decide +kernel
      have hl : raw15088step1Labels = raw15088step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15088step0 raw15088step0Labels permutation32 permutation3
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw15089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15089Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15089 raw15089Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw15089 raw15089Labels = mixedMoment B raw15089step0 raw15089step0Labels := by
      have ha : raw15089step0 = (fun i j => raw15089 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15089step0 raw15089; decide +kernel
      have hl : raw15089step0Labels = raw15089Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15089 raw15089Labels permutation176 permutation3
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw15090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15090Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15090step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15090 raw15090Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw15090 raw15090Labels = mixedMoment B raw15090step0 raw15090step0Labels := by
      have hz : ∀ j, raw15090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15090step0 = (fun i j => raw15090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15090step0 raw15090; decide +kernel
      have hl : raw15090step0Labels = raw15090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15090 raw15090Labels permutation346 hz
    mixedMoment B raw15090step0 raw15090step0Labels = mixedMoment B raw15090step1 raw15090step1Labels := by
      have ha : raw15090step1 = (fun i j => raw15090step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15090step1 raw15090step0; decide +kernel
      have hl : raw15090step1Labels = raw15090step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15090step0 raw15090step0Labels permutation38 permutation3
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw15091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15091Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15091step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw15091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15091 raw15091Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw15091 raw15091Labels = mixedMoment B raw15091step0 raw15091step0Labels := by
      have hz : ∀ j, raw15091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15091step0 = (fun i j => raw15091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15091step0 raw15091; decide +kernel
      have hl : raw15091step0Labels = raw15091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15091 raw15091Labels permutation346 hz
    mixedMoment B raw15091step0 raw15091step0Labels = mixedMoment B raw15091step1 raw15091step1Labels := by
      have ha : raw15091step1 = (fun i j => raw15091step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15091step1 raw15091step0; decide +kernel
      have hl : raw15091step1Labels = raw15091step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15091step0 raw15091step0Labels permutation44 permutation3
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw15092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15092Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15092step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw15092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15092 raw15092Labels = mixedMoment B node3911 node3911Labels := by
  calc
    mixedMoment B raw15092 raw15092Labels = mixedMoment B raw15092step0 raw15092step0Labels := by
      have hz : ∀ j, raw15092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15092step0 = (fun i j => raw15092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15092step0 raw15092; decide +kernel
      have hl : raw15092step0Labels = raw15092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15092 raw15092Labels permutation346 hz
    mixedMoment B raw15092step0 raw15092step0Labels = mixedMoment B raw15092step1 raw15092step1Labels := by
      have ha : raw15092step1 = (fun i j => raw15092step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15092step1 raw15092step0; decide +kernel
      have hl : raw15092step1Labels = raw15092step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15092step0 raw15092step0Labels permutation32 permutation3
    _ = mixedMoment B node3911 node3911Labels := by rfl

def raw15093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15093Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15093 raw15093Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw15093 raw15093Labels = mixedMoment B raw15093step0 raw15093step0Labels := by
      have ha : raw15093step0 = (fun i j => raw15093 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15093step0 raw15093; decide +kernel
      have hl : raw15093step0Labels = raw15093Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15093 raw15093Labels permutation160 permutation3
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw15094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15094Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15094 raw15094Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw15094 raw15094Labels = mixedMoment B raw15094step0 raw15094step0Labels := by
      have ha : raw15094step0 = (fun i j => raw15094 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15094step0 raw15094; decide +kernel
      have hl : raw15094step0Labels = raw15094Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15094 raw15094Labels permutation160 permutation3
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw15095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15095Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15095 raw15095Labels = mixedMoment B node3821 node3821Labels := by
  calc
    mixedMoment B raw15095 raw15095Labels = mixedMoment B raw15095step0 raw15095step0Labels := by
      have ha : raw15095step0 = (fun i j => raw15095 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15095step0 raw15095; decide +kernel
      have hl : raw15095step0Labels = raw15095Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15095 raw15095Labels permutation160 permutation3
    _ = mixedMoment B node3821 node3821Labels := by rfl

def raw15096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15096Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15096 raw15096Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw15096 raw15096Labels = mixedMoment B raw15096step0 raw15096step0Labels := by
      have ha : raw15096step0 = (fun i j => raw15096 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15096step0 raw15096; decide +kernel
      have hl : raw15096step0Labels = raw15096Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15096 raw15096Labels permutation166 permutation3
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw15097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15097Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15097 raw15097Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw15097 raw15097Labels = mixedMoment B raw15097step0 raw15097step0Labels := by
      have ha : raw15097step0 = (fun i j => raw15097 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15097step0 raw15097; decide +kernel
      have hl : raw15097step0Labels = raw15097Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15097 raw15097Labels permutation161 permutation3
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw15098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15098Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15098step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15098 raw15098Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw15098 raw15098Labels = mixedMoment B raw15098step0 raw15098step0Labels := by
      have hz : ∀ j, raw15098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15098step0 = (fun i j => raw15098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15098step0 raw15098; decide +kernel
      have hl : raw15098step0Labels = raw15098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15098 raw15098Labels permutation346 hz
    mixedMoment B raw15098step0 raw15098step0Labels = mixedMoment B raw15098step1 raw15098step1Labels := by
      have ha : raw15098step1 = (fun i j => raw15098step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15098step1 raw15098step0; decide +kernel
      have hl : raw15098step1Labels = raw15098step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15098step0 raw15098step0Labels permutation34 permutation3
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw15099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15099Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15099step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15099 raw15099Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw15099 raw15099Labels = mixedMoment B raw15099step0 raw15099step0Labels := by
      have hz : ∀ j, raw15099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15099step0 = (fun i j => raw15099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15099step0 raw15099; decide +kernel
      have hl : raw15099step0Labels = raw15099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15099 raw15099Labels permutation346 hz
    mixedMoment B raw15099step0 raw15099step0Labels = mixedMoment B raw15099step1 raw15099step1Labels := by
      have ha : raw15099step1 = (fun i j => raw15099step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15099step1 raw15099step0; decide +kernel
      have hl : raw15099step1Labels = raw15099step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15099step0 raw15099step0Labels permutation34 permutation3
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw15100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15100 raw15100Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw15100 raw15100Labels = mixedMoment B raw15100step0 raw15100step0Labels := by
      have ha : raw15100step0 = (fun i j => raw15100 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15100step0 raw15100; decide +kernel
      have hl : raw15100step0Labels = raw15100Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15100 raw15100Labels permutation178 permutation3
    _ = mixedMoment B node3781 node3781Labels := by rfl

def raw15101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15101step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15101 raw15101Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw15101 raw15101Labels = mixedMoment B raw15101step0 raw15101step0Labels := by
      have hz : ∀ j, raw15101 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15101step0 = (fun i j => raw15101 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15101step0 raw15101; decide +kernel
      have hl : raw15101step0Labels = raw15101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15101 raw15101Labels permutation346 hz
    mixedMoment B raw15101step0 raw15101step0Labels = mixedMoment B raw15101step1 raw15101step1Labels := by
      have ha : raw15101step1 = (fun i j => raw15101step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15101step1 raw15101step0; decide +kernel
      have hl : raw15101step1Labels = raw15101step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15101step0 raw15101step0Labels permutation34 permutation3
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw15102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15102 raw15102Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw15102 raw15102Labels = mixedMoment B raw15102step0 raw15102step0Labels := by
      have hz : ∀ j, raw15102 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15102step0 = (fun i j => raw15102 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15102step0 raw15102; decide +kernel
      have hl : raw15102step0Labels = raw15102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15102 raw15102Labels permutation346 hz
    mixedMoment B raw15102step0 raw15102step0Labels = mixedMoment B raw15102step1 raw15102step1Labels := by
      have ha : raw15102step1 = (fun i j => raw15102step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15102step1 raw15102step0; decide +kernel
      have hl : raw15102step1Labels = raw15102step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15102step0 raw15102step0Labels permutation35 permutation3
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw15103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15103 raw15103Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw15103 raw15103Labels = mixedMoment B raw15103step0 raw15103step0Labels := by
      have hz : ∀ j, raw15103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15103step0 = (fun i j => raw15103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15103step0 raw15103; decide +kernel
      have hl : raw15103step0Labels = raw15103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15103 raw15103Labels permutation346 hz
    mixedMoment B raw15103step0 raw15103step0Labels = mixedMoment B raw15103step1 raw15103step1Labels := by
      have ha : raw15103step1 = (fun i j => raw15103step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15103step1 raw15103step0; decide +kernel
      have hl : raw15103step1Labels = raw15103step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15103step0 raw15103step0Labels permutation32 permutation3
    _ = mixedMoment B node2029 node2029Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
