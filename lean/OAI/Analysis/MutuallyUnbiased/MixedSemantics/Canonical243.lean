import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw31104step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31104 raw31104Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw31104 raw31104Labels = mixedMoment B raw31104step0 raw31104step0Labels := by
      have hz : ∀ j, raw31104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31104step0 = (fun i j => raw31104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31104step0 raw31104; decide +kernel
      have hl : raw31104step0Labels = raw31104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31104 raw31104Labels permutation434 hz
    mixedMoment B raw31104step0 raw31104step0Labels = mixedMoment B raw31104step1 raw31104step1Labels := by
      have hz : ∀ j, raw31104step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31104step1 = (fun i j => raw31104step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31104step1 raw31104step0; decide +kernel
      have hl : raw31104step1Labels = raw31104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31104step0 raw31104step0Labels permutation80 hz
    mixedMoment B raw31104step1 raw31104step1Labels = mixedMoment B raw31104step2 raw31104step2Labels := by
      have ha : raw31104step2 = (fun i j => raw31104step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31104step2 raw31104step1; decide +kernel
      have hl : raw31104step2Labels = raw31104step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31104step1 raw31104step1Labels permutation9 permutation6
    _ = mixedMoment B node1653 node1653Labels := by rfl

def raw31105 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw31105step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31105 raw31105Labels = mixedMoment B node2066 node2066Labels := by
  calc
    mixedMoment B raw31105 raw31105Labels = mixedMoment B raw31105step0 raw31105step0Labels := by
      have hz : ∀ j, raw31105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31105step0 = (fun i j => raw31105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31105step0 raw31105; decide +kernel
      have hl : raw31105step0Labels = raw31105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31105 raw31105Labels permutation434 hz
    mixedMoment B raw31105step0 raw31105step0Labels = mixedMoment B raw31105step1 raw31105step1Labels := by
      have hz : ∀ j, raw31105step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31105step1 = (fun i j => raw31105step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31105step1 raw31105step0; decide +kernel
      have hl : raw31105step1Labels = raw31105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31105step0 raw31105step0Labels permutation80 hz
    mixedMoment B raw31105step1 raw31105step1Labels = mixedMoment B raw31105step2 raw31105step2Labels := by
      have ha : raw31105step2 = (fun i j => raw31105step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31105step2 raw31105step1; decide +kernel
      have hl : raw31105step2Labels = raw31105step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31105step1 raw31105step1Labels permutation9 permutation6
    _ = mixedMoment B node2066 node2066Labels := by rfl

def raw31106 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31106 raw31106Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw31106 raw31106Labels = mixedMoment B raw31106step0 raw31106step0Labels := by
      have hz : ∀ j, raw31106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31106step0 = (fun i j => raw31106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31106step0 raw31106; decide +kernel
      have hl : raw31106step0Labels = raw31106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31106 raw31106Labels permutation434 hz
    mixedMoment B raw31106step0 raw31106step0Labels = mixedMoment B raw31106step1 raw31106step1Labels := by
      have ha : raw31106step1 = (fun i j => raw31106step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31106step1 raw31106step0; decide +kernel
      have hl : raw31106step1Labels = raw31106step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31106step0 raw31106step0Labels permutation33 permutation6
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw31107 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31107step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31107 raw31107Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw31107 raw31107Labels = mixedMoment B raw31107step0 raw31107step0Labels := by
      have hz : ∀ j, raw31107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31107step0 = (fun i j => raw31107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31107step0 raw31107; decide +kernel
      have hl : raw31107step0Labels = raw31107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31107 raw31107Labels permutation346 hz
    mixedMoment B raw31107step0 raw31107step0Labels = mixedMoment B raw31107step1 raw31107step1Labels := by
      have ha : raw31107step1 = (fun i j => raw31107step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31107step1 raw31107step0; decide +kernel
      have hl : raw31107step1Labels = raw31107step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31107step0 raw31107step0Labels permutation33 permutation6
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw31108 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31108step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31108step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31108step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31108 raw31108Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw31108 raw31108Labels = mixedMoment B raw31108step0 raw31108step0Labels := by
      have hz : ∀ j, raw31108 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31108step0 = (fun i j => raw31108 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31108step0 raw31108; decide +kernel
      have hl : raw31108step0Labels = raw31108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31108 raw31108Labels permutation434 hz
    mixedMoment B raw31108step0 raw31108step0Labels = mixedMoment B raw31108step1 raw31108step1Labels := by
      have hz : ∀ j, raw31108step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31108step1 = (fun i j => raw31108step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31108step1 raw31108step0; decide +kernel
      have hl : raw31108step1Labels = raw31108step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31108step0 raw31108step0Labels permutation80 hz
    mixedMoment B raw31108step1 raw31108step1Labels = mixedMoment B raw31108step2 raw31108step2Labels := by
      have ha : raw31108step2 = (fun i j => raw31108step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31108step2 raw31108step1; decide +kernel
      have hl : raw31108step2Labels = raw31108step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31108step1 raw31108step1Labels permutation8 permutation6
    _ = mixedMoment B node2116 node2116Labels := by rfl

def raw31109 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31109Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31109step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw31109step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31109step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31109step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31109step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31109 raw31109Labels = mixedMoment B node2968 node2968Labels := by
  calc
    mixedMoment B raw31109 raw31109Labels = mixedMoment B raw31109step0 raw31109step0Labels := by
      have hz : ∀ j, raw31109 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31109step0 = (fun i j => raw31109 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31109step0 raw31109; decide +kernel
      have hl : raw31109step0Labels = raw31109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31109 raw31109Labels permutation434 hz
    mixedMoment B raw31109step0 raw31109step0Labels = mixedMoment B raw31109step1 raw31109step1Labels := by
      have hz : ∀ j, raw31109step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31109step1 = (fun i j => raw31109step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31109step1 raw31109step0; decide +kernel
      have hl : raw31109step1Labels = raw31109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31109step0 raw31109step0Labels permutation80 hz
    mixedMoment B raw31109step1 raw31109step1Labels = mixedMoment B raw31109step2 raw31109step2Labels := by
      have ha : raw31109step2 = (fun i j => raw31109step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31109step2 raw31109step1; decide +kernel
      have hl : raw31109step2Labels = raw31109step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31109step1 raw31109step1Labels permutation8 permutation7
    mixedMoment B raw31109step2 raw31109step2Labels = mixedMoment B raw31109step3 raw31109step3Labels := by
      have ha : raw31109step3 = raw31109step2 := by apply Matrix.ext; unfold raw31109step3 raw31109step2; decide +kernel
      have hl : raw31109step2Labels = labelEmbedding1 ∘ raw31109step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31109step2 raw31109step2Labels raw31109step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2968 node2968Labels := by rfl

def raw31110 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31110step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31110step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31110 raw31110Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw31110 raw31110Labels = mixedMoment B raw31110step0 raw31110step0Labels := by
      have hz : ∀ j, raw31110 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31110step0 = (fun i j => raw31110 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31110step0 raw31110; decide +kernel
      have hl : raw31110step0Labels = raw31110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31110 raw31110Labels permutation434 hz
    mixedMoment B raw31110step0 raw31110step0Labels = mixedMoment B raw31110step1 raw31110step1Labels := by
      have ha : raw31110step1 = (fun i j => raw31110step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31110step1 raw31110step0; decide +kernel
      have hl : raw31110step1Labels = raw31110step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31110step0 raw31110step0Labels permutation32 permutation7
    mixedMoment B raw31110step1 raw31110step1Labels = mixedMoment B raw31110step2 raw31110step2Labels := by
      have ha : raw31110step2 = raw31110step1 := by apply Matrix.ext; unfold raw31110step2 raw31110step1; decide +kernel
      have hl : raw31110step1Labels = labelEmbedding1 ∘ raw31110step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31110step1 raw31110step1Labels raw31110step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2867 node2867Labels := by rfl

def raw31111 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31111step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31111step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31111 raw31111Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw31111 raw31111Labels = mixedMoment B raw31111step0 raw31111step0Labels := by
      have hz : ∀ j, raw31111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31111step0 = (fun i j => raw31111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31111step0 raw31111; decide +kernel
      have hl : raw31111step0Labels = raw31111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31111 raw31111Labels permutation346 hz
    mixedMoment B raw31111step0 raw31111step0Labels = mixedMoment B raw31111step1 raw31111step1Labels := by
      have ha : raw31111step1 = (fun i j => raw31111step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31111step1 raw31111step0; decide +kernel
      have hl : raw31111step1Labels = raw31111step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31111step0 raw31111step0Labels permutation32 permutation7
    mixedMoment B raw31111step1 raw31111step1Labels = mixedMoment B raw31111step2 raw31111step2Labels := by
      have ha : raw31111step2 = raw31111step1 := by apply Matrix.ext; unfold raw31111step2 raw31111step1; decide +kernel
      have hl : raw31111step1Labels = labelEmbedding1 ∘ raw31111step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31111step1 raw31111step1Labels raw31111step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2867 node2867Labels := by rfl

def raw31112 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31112step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31112step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw31112step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31112step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw31112step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31112 raw31112Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw31112 raw31112Labels = mixedMoment B raw31112step0 raw31112step0Labels := by
      have hz : ∀ j, raw31112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31112step0 = (fun i j => raw31112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31112step0 raw31112; decide +kernel
      have hl : raw31112step0Labels = raw31112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31112 raw31112Labels permutation434 hz
    mixedMoment B raw31112step0 raw31112step0Labels = mixedMoment B raw31112step1 raw31112step1Labels := by
      have hz : ∀ j, raw31112step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31112step1 = (fun i j => raw31112step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31112step1 raw31112step0; decide +kernel
      have hl : raw31112step1Labels = raw31112step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31112step0 raw31112step0Labels permutation80 hz
    mixedMoment B raw31112step1 raw31112step1Labels = mixedMoment B raw31112step2 raw31112step2Labels := by
      have ha : raw31112step2 = (fun i j => raw31112step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31112step2 raw31112step1; decide +kernel
      have hl : raw31112step2Labels = raw31112step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31112step1 raw31112step1Labels permutation8 permutation7
    mixedMoment B raw31112step2 raw31112step2Labels = mixedMoment B raw31112step3 raw31112step3Labels := by
      have ha : raw31112step3 = raw31112step2 := by apply Matrix.ext; unfold raw31112step3 raw31112step2; decide +kernel
      have hl : raw31112step2Labels = labelEmbedding1 ∘ raw31112step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31112step2 raw31112step2Labels raw31112step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw31113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31113step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw31113step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw31113step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31113step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw31113step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31113 raw31113Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw31113 raw31113Labels = mixedMoment B raw31113step0 raw31113step0Labels := by
      have hz : ∀ j, raw31113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31113step0 = (fun i j => raw31113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31113step0 raw31113; decide +kernel
      have hl : raw31113step0Labels = raw31113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31113 raw31113Labels permutation434 hz
    mixedMoment B raw31113step0 raw31113step0Labels = mixedMoment B raw31113step1 raw31113step1Labels := by
      have hz : ∀ j, raw31113step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31113step1 = (fun i j => raw31113step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31113step1 raw31113step0; decide +kernel
      have hl : raw31113step1Labels = raw31113step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31113step0 raw31113step0Labels permutation80 hz
    mixedMoment B raw31113step1 raw31113step1Labels = mixedMoment B raw31113step2 raw31113step2Labels := by
      have ha : raw31113step2 = (fun i j => raw31113step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31113step2 raw31113step1; decide +kernel
      have hl : raw31113step2Labels = raw31113step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31113step1 raw31113step1Labels permutation8 permutation7
    mixedMoment B raw31113step2 raw31113step2Labels = mixedMoment B raw31113step3 raw31113step3Labels := by
      have ha : raw31113step3 = raw31113step2 := by apply Matrix.ext; unfold raw31113step3 raw31113step2; decide +kernel
      have hl : raw31113step2Labels = labelEmbedding1 ∘ raw31113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31113step2 raw31113step2Labels raw31113step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2888 node2888Labels := by rfl

def raw31114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31114step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw31114step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-2, 2, 0], ![-2, -1, 3]]
def raw31114step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31114step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def raw31114step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31114step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def raw31114step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31114 raw31114Labels = mixedMoment B node1374 node1374Labels := by
  calc
    mixedMoment B raw31114 raw31114Labels = mixedMoment B raw31114step0 raw31114step0Labels := by
      have hz : ∀ j, raw31114 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31114step0 = (fun i j => raw31114 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31114step0 raw31114; decide +kernel
      have hl : raw31114step0Labels = raw31114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31114 raw31114Labels permutation434 hz
    mixedMoment B raw31114step0 raw31114step0Labels = mixedMoment B raw31114step1 raw31114step1Labels := by
      have hz : ∀ j, raw31114step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31114step1 = (fun i j => raw31114step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31114step1 raw31114step0; decide +kernel
      have hl : raw31114step1Labels = raw31114step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31114step0 raw31114step0Labels permutation80 hz
    mixedMoment B raw31114step1 raw31114step1Labels = mixedMoment B raw31114step2 raw31114step2Labels := by
      have ha : raw31114step2 = (fun i j => raw31114step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31114step2 raw31114step1; decide +kernel
      have hl : raw31114step2Labels = raw31114step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31114step1 raw31114step1Labels permutation13 permutation5
    mixedMoment B raw31114step2 raw31114step2Labels = mixedMoment B raw31114step3 raw31114step3Labels := by
      have ha : raw31114step3 = -raw31114step2 := by apply Matrix.ext; change ∀ i j, raw31114step3 i j = -(raw31114step2 i j); unfold raw31114step3 raw31114step2; decide +kernel
      have hl : raw31114step3Labels = raw31114step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31114step3 raw31114step3Labels = mixedMoment B raw31114step4 raw31114step4Labels := by
      have ha : raw31114step4 = raw31114step3 := by apply Matrix.ext; unfold raw31114step4 raw31114step3; decide +kernel
      have hl : raw31114step3Labels = labelEmbedding1 ∘ raw31114step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31114step3 raw31114step3Labels raw31114step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1374 node1374Labels := by rfl

def raw31115 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31115step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31115 raw31115Labels = mixedMoment B node3151 node3151Labels := by
  calc
    mixedMoment B raw31115 raw31115Labels = mixedMoment B raw31115step0 raw31115step0Labels := by
      have hz : ∀ j, raw31115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31115step0 = (fun i j => raw31115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31115step0 raw31115; decide +kernel
      have hl : raw31115step0Labels = raw31115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31115 raw31115Labels permutation434 hz
    mixedMoment B raw31115step0 raw31115step0Labels = mixedMoment B raw31115step1 raw31115step1Labels := by
      have ha : raw31115step1 = (fun i j => raw31115step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31115step1 raw31115step0; decide +kernel
      have hl : raw31115step1Labels = raw31115step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31115step0 raw31115step0Labels permutation32 permutation7
    mixedMoment B raw31115step1 raw31115step1Labels = mixedMoment B raw31115step2 raw31115step2Labels := by
      have ha : raw31115step2 = raw31115step1 := by apply Matrix.ext; unfold raw31115step2 raw31115step1; decide +kernel
      have hl : raw31115step1Labels = labelEmbedding1 ∘ raw31115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31115step1 raw31115step1Labels raw31115step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3151 node3151Labels := by rfl

def raw31116 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31116step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31116 raw31116Labels = mixedMoment B node3151 node3151Labels := by
  calc
    mixedMoment B raw31116 raw31116Labels = mixedMoment B raw31116step0 raw31116step0Labels := by
      have hz : ∀ j, raw31116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31116step0 = (fun i j => raw31116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31116step0 raw31116; decide +kernel
      have hl : raw31116step0Labels = raw31116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31116 raw31116Labels permutation346 hz
    mixedMoment B raw31116step0 raw31116step0Labels = mixedMoment B raw31116step1 raw31116step1Labels := by
      have ha : raw31116step1 = (fun i j => raw31116step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31116step1 raw31116step0; decide +kernel
      have hl : raw31116step1Labels = raw31116step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31116step0 raw31116step0Labels permutation32 permutation7
    mixedMoment B raw31116step1 raw31116step1Labels = mixedMoment B raw31116step2 raw31116step2Labels := by
      have ha : raw31116step2 = raw31116step1 := by apply Matrix.ext; unfold raw31116step2 raw31116step1; decide +kernel
      have hl : raw31116step1Labels = labelEmbedding1 ∘ raw31116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31116step1 raw31116step1Labels raw31116step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3151 node3151Labels := by rfl

def raw31117 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31117step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31117step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw31117step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31117step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw31117step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31117 raw31117Labels = mixedMoment B node3161 node3161Labels := by
  calc
    mixedMoment B raw31117 raw31117Labels = mixedMoment B raw31117step0 raw31117step0Labels := by
      have hz : ∀ j, raw31117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31117step0 = (fun i j => raw31117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31117step0 raw31117; decide +kernel
      have hl : raw31117step0Labels = raw31117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31117 raw31117Labels permutation434 hz
    mixedMoment B raw31117step0 raw31117step0Labels = mixedMoment B raw31117step1 raw31117step1Labels := by
      have hz : ∀ j, raw31117step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31117step1 = (fun i j => raw31117step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31117step1 raw31117step0; decide +kernel
      have hl : raw31117step1Labels = raw31117step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31117step0 raw31117step0Labels permutation80 hz
    mixedMoment B raw31117step1 raw31117step1Labels = mixedMoment B raw31117step2 raw31117step2Labels := by
      have ha : raw31117step2 = (fun i j => raw31117step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31117step2 raw31117step1; decide +kernel
      have hl : raw31117step2Labels = raw31117step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31117step1 raw31117step1Labels permutation8 permutation7
    mixedMoment B raw31117step2 raw31117step2Labels = mixedMoment B raw31117step3 raw31117step3Labels := by
      have ha : raw31117step3 = raw31117step2 := by apply Matrix.ext; unfold raw31117step3 raw31117step2; decide +kernel
      have hl : raw31117step2Labels = labelEmbedding1 ∘ raw31117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31117step2 raw31117step2Labels raw31117step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3161 node3161Labels := by rfl

def raw31118 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31118step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw31118step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-2, 2, 0], ![-2, -1, 3]]
def raw31118step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31118step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -2, 0], ![2, 1, -3]]
def raw31118step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31118step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -2, 0], ![2, 1, -3]]
def raw31118step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31118 raw31118Labels = mixedMoment B node3160 node3160Labels := by
  calc
    mixedMoment B raw31118 raw31118Labels = mixedMoment B raw31118step0 raw31118step0Labels := by
      have hz : ∀ j, raw31118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31118step0 = (fun i j => raw31118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31118step0 raw31118; decide +kernel
      have hl : raw31118step0Labels = raw31118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31118 raw31118Labels permutation434 hz
    mixedMoment B raw31118step0 raw31118step0Labels = mixedMoment B raw31118step1 raw31118step1Labels := by
      have hz : ∀ j, raw31118step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31118step1 = (fun i j => raw31118step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31118step1 raw31118step0; decide +kernel
      have hl : raw31118step1Labels = raw31118step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31118step0 raw31118step0Labels permutation80 hz
    mixedMoment B raw31118step1 raw31118step1Labels = mixedMoment B raw31118step2 raw31118step2Labels := by
      have ha : raw31118step2 = (fun i j => raw31118step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31118step2 raw31118step1; decide +kernel
      have hl : raw31118step2Labels = raw31118step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31118step1 raw31118step1Labels permutation13 permutation5
    mixedMoment B raw31118step2 raw31118step2Labels = mixedMoment B raw31118step3 raw31118step3Labels := by
      have ha : raw31118step3 = -raw31118step2 := by apply Matrix.ext; change ∀ i j, raw31118step3 i j = -(raw31118step2 i j); unfold raw31118step3 raw31118step2; decide +kernel
      have hl : raw31118step3Labels = raw31118step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31118step3 raw31118step3Labels = mixedMoment B raw31118step4 raw31118step4Labels := by
      have ha : raw31118step4 = raw31118step3 := by apply Matrix.ext; unfold raw31118step4 raw31118step3; decide +kernel
      have hl : raw31118step3Labels = labelEmbedding1 ∘ raw31118step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31118step3 raw31118step3Labels raw31118step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3160 node3160Labels := by rfl

def raw31119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31119step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31119step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31119step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31119step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31119 raw31119Labels = mixedMoment B node1371 node1371Labels := by
  calc
    mixedMoment B raw31119 raw31119Labels = mixedMoment B raw31119step0 raw31119step0Labels := by
      have hz : ∀ j, raw31119 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31119step0 = (fun i j => raw31119 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31119step0 raw31119; decide +kernel
      have hl : raw31119step0Labels = raw31119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31119 raw31119Labels permutation434 hz
    mixedMoment B raw31119step0 raw31119step0Labels = mixedMoment B raw31119step1 raw31119step1Labels := by
      have ha : raw31119step1 = (fun i j => raw31119step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31119step1 raw31119step0; decide +kernel
      have hl : raw31119step1Labels = raw31119step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31119step0 raw31119step0Labels permutation52 permutation5
    mixedMoment B raw31119step1 raw31119step1Labels = mixedMoment B raw31119step2 raw31119step2Labels := by
      have ha : raw31119step2 = -raw31119step1 := by apply Matrix.ext; change ∀ i j, raw31119step2 i j = -(raw31119step1 i j); unfold raw31119step2 raw31119step1; decide +kernel
      have hl : raw31119step2Labels = raw31119step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31119step2 raw31119step2Labels = mixedMoment B raw31119step3 raw31119step3Labels := by
      have ha : raw31119step3 = raw31119step2 := by apply Matrix.ext; unfold raw31119step3 raw31119step2; decide +kernel
      have hl : raw31119step2Labels = labelEmbedding1 ∘ raw31119step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31119step2 raw31119step2Labels raw31119step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1371 node1371Labels := by rfl

def raw31120 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31120step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31120 raw31120Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw31120 raw31120Labels = mixedMoment B raw31120step0 raw31120step0Labels := by
      have hz : ∀ j, raw31120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31120step0 = (fun i j => raw31120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31120step0 raw31120; decide +kernel
      have hl : raw31120step0Labels = raw31120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31120 raw31120Labels permutation434 hz
    mixedMoment B raw31120step0 raw31120step0Labels = mixedMoment B raw31120step1 raw31120step1Labels := by
      have ha : raw31120step1 = (fun i j => raw31120step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31120step1 raw31120step0; decide +kernel
      have hl : raw31120step1Labels = raw31120step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31120step0 raw31120step0Labels permutation32 permutation7
    mixedMoment B raw31120step1 raw31120step1Labels = mixedMoment B raw31120step2 raw31120step2Labels := by
      have ha : raw31120step2 = raw31120step1 := by apply Matrix.ext; unfold raw31120step2 raw31120step1; decide +kernel
      have hl : raw31120step1Labels = labelEmbedding1 ∘ raw31120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31120step1 raw31120step1Labels raw31120step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw31121 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31121Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31121step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31121 raw31121Labels = mixedMoment B node3168 node3168Labels := by
  calc
    mixedMoment B raw31121 raw31121Labels = mixedMoment B raw31121step0 raw31121step0Labels := by
      have ha : raw31121step0 = (fun i j => raw31121 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31121step0 raw31121; decide +kernel
      have hl : raw31121step0Labels = raw31121Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31121 raw31121Labels permutation152 permutation7
    mixedMoment B raw31121step0 raw31121step0Labels = mixedMoment B raw31121step1 raw31121step1Labels := by
      have ha : raw31121step1 = raw31121step0 := by apply Matrix.ext; unfold raw31121step1 raw31121step0; decide +kernel
      have hl : raw31121step0Labels = labelEmbedding1 ∘ raw31121step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31121step0 raw31121step0Labels raw31121step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3168 node3168Labels := by rfl

def raw31122 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31122Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31122step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31122step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31122 raw31122Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw31122 raw31122Labels = mixedMoment B raw31122step0 raw31122step0Labels := by
      have hz : ∀ j, raw31122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31122step0 = (fun i j => raw31122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31122step0 raw31122; decide +kernel
      have hl : raw31122step0Labels = raw31122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31122 raw31122Labels permutation434 hz
    mixedMoment B raw31122step0 raw31122step0Labels = mixedMoment B raw31122step1 raw31122step1Labels := by
      have ha : raw31122step1 = (fun i j => raw31122step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31122step1 raw31122step0; decide +kernel
      have hl : raw31122step1Labels = raw31122step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31122step0 raw31122step0Labels permutation32 permutation7
    mixedMoment B raw31122step1 raw31122step1Labels = mixedMoment B raw31122step2 raw31122step2Labels := by
      have ha : raw31122step2 = raw31122step1 := by apply Matrix.ext; unfold raw31122step2 raw31122step1; decide +kernel
      have hl : raw31122step1Labels = labelEmbedding1 ∘ raw31122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31122step1 raw31122step1Labels raw31122step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3174 node3174Labels := by rfl

def raw31123 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31123Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31123step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31123step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31123step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31123step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31123step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31123 raw31123Labels = mixedMoment B node3159 node3159Labels := by
  calc
    mixedMoment B raw31123 raw31123Labels = mixedMoment B raw31123step0 raw31123step0Labels := by
      have hz : ∀ j, raw31123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31123step0 = (fun i j => raw31123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31123step0 raw31123; decide +kernel
      have hl : raw31123step0Labels = raw31123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31123 raw31123Labels permutation434 hz
    mixedMoment B raw31123step0 raw31123step0Labels = mixedMoment B raw31123step1 raw31123step1Labels := by
      have ha : raw31123step1 = (fun i j => raw31123step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31123step1 raw31123step0; decide +kernel
      have hl : raw31123step1Labels = raw31123step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31123step0 raw31123step0Labels permutation52 permutation5
    mixedMoment B raw31123step1 raw31123step1Labels = mixedMoment B raw31123step2 raw31123step2Labels := by
      have ha : raw31123step2 = -raw31123step1 := by apply Matrix.ext; change ∀ i j, raw31123step2 i j = -(raw31123step1 i j); unfold raw31123step2 raw31123step1; decide +kernel
      have hl : raw31123step2Labels = raw31123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31123step2 raw31123step2Labels = mixedMoment B raw31123step3 raw31123step3Labels := by
      have ha : raw31123step3 = raw31123step2 := by apply Matrix.ext; unfold raw31123step3 raw31123step2; decide +kernel
      have hl : raw31123step2Labels = labelEmbedding1 ∘ raw31123step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31123step2 raw31123step2Labels raw31123step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3159 node3159Labels := by rfl

def raw31124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31124step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31124step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31124step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31124step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31124step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31124 raw31124Labels = mixedMoment B node1371 node1371Labels := by
  calc
    mixedMoment B raw31124 raw31124Labels = mixedMoment B raw31124step0 raw31124step0Labels := by
      have hz : ∀ j, raw31124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31124step0 = (fun i j => raw31124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31124step0 raw31124; decide +kernel
      have hl : raw31124step0Labels = raw31124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31124 raw31124Labels permutation346 hz
    mixedMoment B raw31124step0 raw31124step0Labels = mixedMoment B raw31124step1 raw31124step1Labels := by
      have ha : raw31124step1 = (fun i j => raw31124step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31124step1 raw31124step0; decide +kernel
      have hl : raw31124step1Labels = raw31124step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31124step0 raw31124step0Labels permutation52 permutation5
    mixedMoment B raw31124step1 raw31124step1Labels = mixedMoment B raw31124step2 raw31124step2Labels := by
      have ha : raw31124step2 = -raw31124step1 := by apply Matrix.ext; change ∀ i j, raw31124step2 i j = -(raw31124step1 i j); unfold raw31124step2 raw31124step1; decide +kernel
      have hl : raw31124step2Labels = raw31124step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31124step2 raw31124step2Labels = mixedMoment B raw31124step3 raw31124step3Labels := by
      have ha : raw31124step3 = raw31124step2 := by apply Matrix.ext; unfold raw31124step3 raw31124step2; decide +kernel
      have hl : raw31124step2Labels = labelEmbedding1 ∘ raw31124step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31124step2 raw31124step2Labels raw31124step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1371 node1371Labels := by rfl

def raw31125 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31125Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31125step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31125step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31125 raw31125Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw31125 raw31125Labels = mixedMoment B raw31125step0 raw31125step0Labels := by
      have hz : ∀ j, raw31125 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31125step0 = (fun i j => raw31125 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31125step0 raw31125; decide +kernel
      have hl : raw31125step0Labels = raw31125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31125 raw31125Labels permutation346 hz
    mixedMoment B raw31125step0 raw31125step0Labels = mixedMoment B raw31125step1 raw31125step1Labels := by
      have ha : raw31125step1 = (fun i j => raw31125step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31125step1 raw31125step0; decide +kernel
      have hl : raw31125step1Labels = raw31125step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31125step0 raw31125step0Labels permutation32 permutation7
    mixedMoment B raw31125step1 raw31125step1Labels = mixedMoment B raw31125step2 raw31125step2Labels := by
      have ha : raw31125step2 = raw31125step1 := by apply Matrix.ext; unfold raw31125step2 raw31125step1; decide +kernel
      have hl : raw31125step1Labels = labelEmbedding1 ∘ raw31125step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31125step1 raw31125step1Labels raw31125step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw31126 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31126step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31126step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31126 raw31126Labels = mixedMoment B node3168 node3168Labels := by
  calc
    mixedMoment B raw31126 raw31126Labels = mixedMoment B raw31126step0 raw31126step0Labels := by
      have ha : raw31126step0 = (fun i j => raw31126 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31126step0 raw31126; decide +kernel
      have hl : raw31126step0Labels = raw31126Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31126 raw31126Labels permutation158 permutation7
    mixedMoment B raw31126step0 raw31126step0Labels = mixedMoment B raw31126step1 raw31126step1Labels := by
      have ha : raw31126step1 = raw31126step0 := by apply Matrix.ext; unfold raw31126step1 raw31126step0; decide +kernel
      have hl : raw31126step0Labels = labelEmbedding1 ∘ raw31126step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31126step0 raw31126step0Labels raw31126step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3168 node3168Labels := by rfl

def raw31127 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31127Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31127step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31127step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31127 raw31127Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw31127 raw31127Labels = mixedMoment B raw31127step0 raw31127step0Labels := by
      have hz : ∀ j, raw31127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31127step0 = (fun i j => raw31127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31127step0 raw31127; decide +kernel
      have hl : raw31127step0Labels = raw31127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31127 raw31127Labels permutation346 hz
    mixedMoment B raw31127step0 raw31127step0Labels = mixedMoment B raw31127step1 raw31127step1Labels := by
      have ha : raw31127step1 = (fun i j => raw31127step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31127step1 raw31127step0; decide +kernel
      have hl : raw31127step1Labels = raw31127step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31127step0 raw31127step0Labels permutation32 permutation7
    mixedMoment B raw31127step1 raw31127step1Labels = mixedMoment B raw31127step2 raw31127step2Labels := by
      have ha : raw31127step2 = raw31127step1 := by apply Matrix.ext; unfold raw31127step2 raw31127step1; decide +kernel
      have hl : raw31127step1Labels = labelEmbedding1 ∘ raw31127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31127step1 raw31127step1Labels raw31127step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3174 node3174Labels := by rfl

def raw31128 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31128Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31128step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31128step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31128step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31128step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31128 raw31128Labels = mixedMoment B node3159 node3159Labels := by
  calc
    mixedMoment B raw31128 raw31128Labels = mixedMoment B raw31128step0 raw31128step0Labels := by
      have hz : ∀ j, raw31128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31128step0 = (fun i j => raw31128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31128step0 raw31128; decide +kernel
      have hl : raw31128step0Labels = raw31128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31128 raw31128Labels permutation346 hz
    mixedMoment B raw31128step0 raw31128step0Labels = mixedMoment B raw31128step1 raw31128step1Labels := by
      have ha : raw31128step1 = (fun i j => raw31128step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31128step1 raw31128step0; decide +kernel
      have hl : raw31128step1Labels = raw31128step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31128step0 raw31128step0Labels permutation52 permutation5
    mixedMoment B raw31128step1 raw31128step1Labels = mixedMoment B raw31128step2 raw31128step2Labels := by
      have ha : raw31128step2 = -raw31128step1 := by apply Matrix.ext; change ∀ i j, raw31128step2 i j = -(raw31128step1 i j); unfold raw31128step2 raw31128step1; decide +kernel
      have hl : raw31128step2Labels = raw31128step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31128step2 raw31128step2Labels = mixedMoment B raw31128step3 raw31128step3Labels := by
      have ha : raw31128step3 = raw31128step2 := by apply Matrix.ext; unfold raw31128step3 raw31128step2; decide +kernel
      have hl : raw31128step2Labels = labelEmbedding1 ∘ raw31128step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31128step2 raw31128step2Labels raw31128step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3159 node3159Labels := by rfl

def raw31129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31129Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31129step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -3, 2], ![-2, 0, 2]]
def raw31129step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, -1, 2], ![-3, 2, 1]]
def raw31129step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw31129step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31129step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def raw31129step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31129 raw31129Labels = mixedMoment B node1373 node1373Labels := by
  calc
    mixedMoment B raw31129 raw31129Labels = mixedMoment B raw31129step0 raw31129step0Labels := by
      have hz : ∀ j, raw31129 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31129step0 = (fun i j => raw31129 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31129step0 raw31129; decide +kernel
      have hl : raw31129step0Labels = raw31129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31129 raw31129Labels permutation434 hz
    mixedMoment B raw31129step0 raw31129step0Labels = mixedMoment B raw31129step1 raw31129step1Labels := by
      have hz : ∀ j, raw31129step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31129step1 = (fun i j => raw31129step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31129step1 raw31129step0; decide +kernel
      have hl : raw31129step1Labels = raw31129step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31129step0 raw31129step0Labels permutation80 hz
    mixedMoment B raw31129step1 raw31129step1Labels = mixedMoment B raw31129step2 raw31129step2Labels := by
      have ha : raw31129step2 = (fun i j => raw31129step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31129step2 raw31129step1; decide +kernel
      have hl : raw31129step2Labels = raw31129step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31129step1 raw31129step1Labels permutation12 permutation5
    mixedMoment B raw31129step2 raw31129step2Labels = mixedMoment B raw31129step3 raw31129step3Labels := by
      have ha : raw31129step3 = -raw31129step2 := by apply Matrix.ext; change ∀ i j, raw31129step3 i j = -(raw31129step2 i j); unfold raw31129step3 raw31129step2; decide +kernel
      have hl : raw31129step3Labels = raw31129step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31129step3 raw31129step3Labels = mixedMoment B raw31129step4 raw31129step4Labels := by
      have ha : raw31129step4 = raw31129step3 := by apply Matrix.ext; unfold raw31129step4 raw31129step3; decide +kernel
      have hl : raw31129step3Labels = labelEmbedding1 ∘ raw31129step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31129step3 raw31129step3Labels raw31129step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1373 node1373Labels := by rfl

def raw31130 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31130step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -3, 2], ![-2, 0, 2]]
def raw31130step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31130step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw31130step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31130step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw31130step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31130 raw31130Labels = mixedMoment B node3095 node3095Labels := by
  calc
    mixedMoment B raw31130 raw31130Labels = mixedMoment B raw31130step0 raw31130step0Labels := by
      have hz : ∀ j, raw31130 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31130step0 = (fun i j => raw31130 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31130step0 raw31130; decide +kernel
      have hl : raw31130step0Labels = raw31130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31130 raw31130Labels permutation434 hz
    mixedMoment B raw31130step0 raw31130step0Labels = mixedMoment B raw31130step1 raw31130step1Labels := by
      have hz : ∀ j, raw31130step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31130step1 = (fun i j => raw31130step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31130step1 raw31130step0; decide +kernel
      have hl : raw31130step1Labels = raw31130step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31130step0 raw31130step0Labels permutation80 hz
    mixedMoment B raw31130step1 raw31130step1Labels = mixedMoment B raw31130step2 raw31130step2Labels := by
      have ha : raw31130step2 = (fun i j => raw31130step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31130step2 raw31130step1; decide +kernel
      have hl : raw31130step2Labels = raw31130step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31130step1 raw31130step1Labels permutation23 permutation5
    mixedMoment B raw31130step2 raw31130step2Labels = mixedMoment B raw31130step3 raw31130step3Labels := by
      have ha : raw31130step3 = raw31130step2 := by apply Matrix.ext; unfold raw31130step3 raw31130step2; decide +kernel
      have hl : raw31130step2Labels = labelEmbedding1 ∘ raw31130step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31130step2 raw31130step2Labels raw31130step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3095 node3095Labels := by rfl

def raw31131 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31131step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw31131step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw31131step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31131 raw31131Labels = mixedMoment B node2872 node2872Labels := by
  calc
    mixedMoment B raw31131 raw31131Labels = mixedMoment B raw31131step0 raw31131step0Labels := by
      have hz : ∀ j, raw31131 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31131step0 = (fun i j => raw31131 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31131step0 raw31131; decide +kernel
      have hl : raw31131step0Labels = raw31131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31131 raw31131Labels permutation434 hz
    mixedMoment B raw31131step0 raw31131step0Labels = mixedMoment B raw31131step1 raw31131step1Labels := by
      have ha : raw31131step1 = (fun i j => raw31131step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31131step1 raw31131step0; decide +kernel
      have hl : raw31131step1Labels = raw31131step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31131step0 raw31131step0Labels permutation115 permutation5
    mixedMoment B raw31131step1 raw31131step1Labels = mixedMoment B raw31131step2 raw31131step2Labels := by
      have ha : raw31131step2 = raw31131step1 := by apply Matrix.ext; unfold raw31131step2 raw31131step1; decide +kernel
      have hl : raw31131step1Labels = labelEmbedding1 ∘ raw31131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31131step1 raw31131step1Labels raw31131step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2872 node2872Labels := by rfl

def raw31132 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31132step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw31132step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw31132step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31132 raw31132Labels = mixedMoment B node2872 node2872Labels := by
  calc
    mixedMoment B raw31132 raw31132Labels = mixedMoment B raw31132step0 raw31132step0Labels := by
      have hz : ∀ j, raw31132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31132step0 = (fun i j => raw31132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31132step0 raw31132; decide +kernel
      have hl : raw31132step0Labels = raw31132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31132 raw31132Labels permutation346 hz
    mixedMoment B raw31132step0 raw31132step0Labels = mixedMoment B raw31132step1 raw31132step1Labels := by
      have ha : raw31132step1 = (fun i j => raw31132step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31132step1 raw31132step0; decide +kernel
      have hl : raw31132step1Labels = raw31132step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31132step0 raw31132step0Labels permutation115 permutation5
    mixedMoment B raw31132step1 raw31132step1Labels = mixedMoment B raw31132step2 raw31132step2Labels := by
      have ha : raw31132step2 = raw31132step1 := by apply Matrix.ext; unfold raw31132step2 raw31132step1; decide +kernel
      have hl : raw31132step1Labels = labelEmbedding1 ∘ raw31132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31132step1 raw31132step1Labels raw31132step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2872 node2872Labels := by rfl

def raw31133 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31133Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31133step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -3, 2], ![-3, 1, 2]]
def raw31133step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 2, -3], ![3, -3, 0]]
def raw31133step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 2, -3], ![3, -3, 0]]
def raw31133step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31133 raw31133Labels = mixedMoment B node2887 node2887Labels := by
  calc
    mixedMoment B raw31133 raw31133Labels = mixedMoment B raw31133step0 raw31133step0Labels := by
      have hz : ∀ j, raw31133 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31133step0 = (fun i j => raw31133 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31133step0 raw31133; decide +kernel
      have hl : raw31133step0Labels = raw31133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31133 raw31133Labels permutation434 hz
    mixedMoment B raw31133step0 raw31133step0Labels = mixedMoment B raw31133step1 raw31133step1Labels := by
      have hz : ∀ j, raw31133step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31133step1 = (fun i j => raw31133step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31133step1 raw31133step0; decide +kernel
      have hl : raw31133step1Labels = raw31133step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31133step0 raw31133step0Labels permutation80 hz
    mixedMoment B raw31133step1 raw31133step1Labels = mixedMoment B raw31133step2 raw31133step2Labels := by
      have ha : raw31133step2 = (fun i j => raw31133step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31133step2 raw31133step1; decide +kernel
      have hl : raw31133step2Labels = raw31133step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31133step1 raw31133step1Labels permutation23 permutation5
    mixedMoment B raw31133step2 raw31133step2Labels = mixedMoment B raw31133step3 raw31133step3Labels := by
      have ha : raw31133step3 = raw31133step2 := by apply Matrix.ext; unfold raw31133step3 raw31133step2; decide +kernel
      have hl : raw31133step2Labels = labelEmbedding1 ∘ raw31133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31133step2 raw31133step2Labels raw31133step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2887 node2887Labels := by rfl

def raw31134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31134step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw31134step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31134step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31134step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw31134step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31134step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw31134step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31134 raw31134Labels = mixedMoment B node1444 node1444Labels := by
  calc
    mixedMoment B raw31134 raw31134Labels = mixedMoment B raw31134step0 raw31134step0Labels := by
      have hz : ∀ j, raw31134 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31134step0 = (fun i j => raw31134 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31134step0 raw31134; decide +kernel
      have hl : raw31134step0Labels = raw31134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31134 raw31134Labels permutation434 hz
    mixedMoment B raw31134step0 raw31134step0Labels = mixedMoment B raw31134step1 raw31134step1Labels := by
      have hz : ∀ j, raw31134step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31134step1 = (fun i j => raw31134step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31134step1 raw31134step0; decide +kernel
      have hl : raw31134step1Labels = raw31134step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31134step0 raw31134step0Labels permutation80 hz
    mixedMoment B raw31134step1 raw31134step1Labels = mixedMoment B raw31134step2 raw31134step2Labels := by
      have ha : raw31134step2 = (fun i j => raw31134step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31134step2 raw31134step1; decide +kernel
      have hl : raw31134step2Labels = raw31134step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31134step1 raw31134step1Labels permutation12 permutation5
    mixedMoment B raw31134step2 raw31134step2Labels = mixedMoment B raw31134step3 raw31134step3Labels := by
      have ha : raw31134step3 = -raw31134step2 := by apply Matrix.ext; change ∀ i j, raw31134step3 i j = -(raw31134step2 i j); unfold raw31134step3 raw31134step2; decide +kernel
      have hl : raw31134step3Labels = raw31134step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31134step3 raw31134step3Labels = mixedMoment B raw31134step4 raw31134step4Labels := by
      have ha : raw31134step4 = raw31134step3 := by apply Matrix.ext; unfold raw31134step4 raw31134step3; decide +kernel
      have hl : raw31134step3Labels = labelEmbedding1 ∘ raw31134step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31134step3 raw31134step3Labels raw31134step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1444 node1444Labels := by rfl

def raw31135 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31135Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31135step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw31135step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31135step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -2, 0], ![2, -1, -1]]
def raw31135step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31135step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -2, 0], ![2, -1, -1]]
def raw31135step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31135 raw31135Labels = mixedMoment B node3216 node3216Labels := by
  calc
    mixedMoment B raw31135 raw31135Labels = mixedMoment B raw31135step0 raw31135step0Labels := by
      have hz : ∀ j, raw31135 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31135step0 = (fun i j => raw31135 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31135step0 raw31135; decide +kernel
      have hl : raw31135step0Labels = raw31135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31135 raw31135Labels permutation434 hz
    mixedMoment B raw31135step0 raw31135step0Labels = mixedMoment B raw31135step1 raw31135step1Labels := by
      have hz : ∀ j, raw31135step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31135step1 = (fun i j => raw31135step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31135step1 raw31135step0; decide +kernel
      have hl : raw31135step1Labels = raw31135step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31135step0 raw31135step0Labels permutation80 hz
    mixedMoment B raw31135step1 raw31135step1Labels = mixedMoment B raw31135step2 raw31135step2Labels := by
      have ha : raw31135step2 = (fun i j => raw31135step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31135step2 raw31135step1; decide +kernel
      have hl : raw31135step2Labels = raw31135step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31135step1 raw31135step1Labels permutation8 permutation7
    mixedMoment B raw31135step2 raw31135step2Labels = mixedMoment B raw31135step3 raw31135step3Labels := by
      have ha : raw31135step3 = raw31135step2 := by apply Matrix.ext; unfold raw31135step3 raw31135step2; decide +kernel
      have hl : raw31135step2Labels = labelEmbedding1 ∘ raw31135step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31135step2 raw31135step2Labels raw31135step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3216 node3216Labels := by rfl

def raw31136 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31136step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31136step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31136step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31136 raw31136Labels = mixedMoment B node3178 node3178Labels := by
  calc
    mixedMoment B raw31136 raw31136Labels = mixedMoment B raw31136step0 raw31136step0Labels := by
      have hz : ∀ j, raw31136 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31136step0 = (fun i j => raw31136 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31136step0 raw31136; decide +kernel
      have hl : raw31136step0Labels = raw31136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31136 raw31136Labels permutation434 hz
    mixedMoment B raw31136step0 raw31136step0Labels = mixedMoment B raw31136step1 raw31136step1Labels := by
      have ha : raw31136step1 = (fun i j => raw31136step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31136step1 raw31136step0; decide +kernel
      have hl : raw31136step1Labels = raw31136step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31136step0 raw31136step0Labels permutation32 permutation7
    mixedMoment B raw31136step1 raw31136step1Labels = mixedMoment B raw31136step2 raw31136step2Labels := by
      have ha : raw31136step2 = raw31136step1 := by apply Matrix.ext; unfold raw31136step2 raw31136step1; decide +kernel
      have hl : raw31136step1Labels = labelEmbedding1 ∘ raw31136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31136step1 raw31136step1Labels raw31136step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3178 node3178Labels := by rfl

def raw31137 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31137Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31137step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31137step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31137step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31137 raw31137Labels = mixedMoment B node3178 node3178Labels := by
  calc
    mixedMoment B raw31137 raw31137Labels = mixedMoment B raw31137step0 raw31137step0Labels := by
      have hz : ∀ j, raw31137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31137step0 = (fun i j => raw31137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31137step0 raw31137; decide +kernel
      have hl : raw31137step0Labels = raw31137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31137 raw31137Labels permutation346 hz
    mixedMoment B raw31137step0 raw31137step0Labels = mixedMoment B raw31137step1 raw31137step1Labels := by
      have ha : raw31137step1 = (fun i j => raw31137step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31137step1 raw31137step0; decide +kernel
      have hl : raw31137step1Labels = raw31137step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31137step0 raw31137step0Labels permutation32 permutation7
    mixedMoment B raw31137step1 raw31137step1Labels = mixedMoment B raw31137step2 raw31137step2Labels := by
      have ha : raw31137step2 = raw31137step1 := by apply Matrix.ext; unfold raw31137step2 raw31137step1; decide +kernel
      have hl : raw31137step1Labels = labelEmbedding1 ∘ raw31137step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31137step1 raw31137step1Labels raw31137step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3178 node3178Labels := by rfl

def raw31138 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31138step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31138step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31138step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw31138step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31138step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw31138step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31138 raw31138Labels = mixedMoment B node3188 node3188Labels := by
  calc
    mixedMoment B raw31138 raw31138Labels = mixedMoment B raw31138step0 raw31138step0Labels := by
      have hz : ∀ j, raw31138 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31138step0 = (fun i j => raw31138 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31138step0 raw31138; decide +kernel
      have hl : raw31138step0Labels = raw31138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31138 raw31138Labels permutation434 hz
    mixedMoment B raw31138step0 raw31138step0Labels = mixedMoment B raw31138step1 raw31138step1Labels := by
      have hz : ∀ j, raw31138step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31138step1 = (fun i j => raw31138step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31138step1 raw31138step0; decide +kernel
      have hl : raw31138step1Labels = raw31138step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31138step0 raw31138step0Labels permutation80 hz
    mixedMoment B raw31138step1 raw31138step1Labels = mixedMoment B raw31138step2 raw31138step2Labels := by
      have ha : raw31138step2 = (fun i j => raw31138step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31138step2 raw31138step1; decide +kernel
      have hl : raw31138step2Labels = raw31138step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31138step1 raw31138step1Labels permutation8 permutation7
    mixedMoment B raw31138step2 raw31138step2Labels = mixedMoment B raw31138step3 raw31138step3Labels := by
      have ha : raw31138step3 = raw31138step2 := by apply Matrix.ext; unfold raw31138step3 raw31138step2; decide +kernel
      have hl : raw31138step2Labels = labelEmbedding1 ∘ raw31138step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31138step2 raw31138step2Labels raw31138step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3188 node3188Labels := by rfl

def raw31139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw31139step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw31139step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31139step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw31139step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31139step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31139 raw31139Labels = mixedMoment B node5303 node5303Labels := by
  calc
    mixedMoment B raw31139 raw31139Labels = mixedMoment B raw31139step0 raw31139step0Labels := by
      have hz : ∀ j, raw31139 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31139step0 = (fun i j => raw31139 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31139step0 raw31139; decide +kernel
      have hl : raw31139step0Labels = raw31139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31139 raw31139Labels permutation434 hz
    mixedMoment B raw31139step0 raw31139step0Labels = mixedMoment B raw31139step1 raw31139step1Labels := by
      have hz : ∀ j, raw31139step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31139step1 = (fun i j => raw31139step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31139step1 raw31139step0; decide +kernel
      have hl : raw31139step1Labels = raw31139step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31139step0 raw31139step0Labels permutation80 hz
    mixedMoment B raw31139step1 raw31139step1Labels = mixedMoment B raw31139step2 raw31139step2Labels := by
      have ha : raw31139step2 = (fun i j => raw31139step1 (permutation14 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31139step2 raw31139step1; decide +kernel
      have hl : raw31139step2Labels = raw31139step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31139step1 raw31139step1Labels permutation14 permutation5
    mixedMoment B raw31139step2 raw31139step2Labels = mixedMoment B raw31139step3 raw31139step3Labels := by
      have ha : raw31139step3 = -raw31139step2 := by apply Matrix.ext; change ∀ i j, raw31139step3 i j = -(raw31139step2 i j); unfold raw31139step3 raw31139step2; decide +kernel
      have hl : raw31139step3Labels = raw31139step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31139step3 raw31139step3Labels = mixedMoment B raw31139step4 raw31139step4Labels := by
      have ha : raw31139step4 = raw31139step3 := by apply Matrix.ext; unfold raw31139step4 raw31139step3; decide +kernel
      have hl : raw31139step3Labels = labelEmbedding8 ∘ raw31139step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31139step3 raw31139step3Labels raw31139step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5303 node5303Labels := by rfl

def raw31140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31140step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31140step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31140step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31140step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31140 raw31140Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw31140 raw31140Labels = mixedMoment B raw31140step0 raw31140step0Labels := by
      have hz : ∀ j, raw31140 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31140step0 = (fun i j => raw31140 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31140step0 raw31140; decide +kernel
      have hl : raw31140step0Labels = raw31140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31140 raw31140Labels permutation434 hz
    mixedMoment B raw31140step0 raw31140step0Labels = mixedMoment B raw31140step1 raw31140step1Labels := by
      have ha : raw31140step1 = (fun i j => raw31140step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31140step1 raw31140step0; decide +kernel
      have hl : raw31140step1Labels = raw31140step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31140step0 raw31140step0Labels permutation38 permutation7
    mixedMoment B raw31140step1 raw31140step1Labels = mixedMoment B raw31140step2 raw31140step2Labels := by
      have ha : raw31140step2 = -raw31140step1 := by apply Matrix.ext; change ∀ i j, raw31140step2 i j = -(raw31140step1 i j); unfold raw31140step2 raw31140step1; decide +kernel
      have hl : raw31140step2Labels = raw31140step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31140step2 raw31140step2Labels = mixedMoment B raw31140step3 raw31140step3Labels := by
      have ha : raw31140step3 = raw31140step2 := by apply Matrix.ext; unfold raw31140step3 raw31140step2; decide +kernel
      have hl : raw31140step2Labels = labelEmbedding10 ∘ raw31140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31140step2 raw31140step2Labels raw31140step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

def raw31141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31141step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31141step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31141step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31141step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31141step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31141 raw31141Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw31141 raw31141Labels = mixedMoment B raw31141step0 raw31141step0Labels := by
      have hz : ∀ j, raw31141 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31141step0 = (fun i j => raw31141 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31141step0 raw31141; decide +kernel
      have hl : raw31141step0Labels = raw31141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31141 raw31141Labels permutation346 hz
    mixedMoment B raw31141step0 raw31141step0Labels = mixedMoment B raw31141step1 raw31141step1Labels := by
      have ha : raw31141step1 = (fun i j => raw31141step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31141step1 raw31141step0; decide +kernel
      have hl : raw31141step1Labels = raw31141step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31141step0 raw31141step0Labels permutation38 permutation7
    mixedMoment B raw31141step1 raw31141step1Labels = mixedMoment B raw31141step2 raw31141step2Labels := by
      have ha : raw31141step2 = -raw31141step1 := by apply Matrix.ext; change ∀ i j, raw31141step2 i j = -(raw31141step1 i j); unfold raw31141step2 raw31141step1; decide +kernel
      have hl : raw31141step2Labels = raw31141step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31141step2 raw31141step2Labels = mixedMoment B raw31141step3 raw31141step3Labels := by
      have ha : raw31141step3 = raw31141step2 := by apply Matrix.ext; unfold raw31141step3 raw31141step2; decide +kernel
      have hl : raw31141step2Labels = labelEmbedding10 ∘ raw31141step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31141step2 raw31141step2Labels raw31141step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

def raw31142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31142step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31142step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31142step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31142step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31142step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31142step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31142step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31142step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31142 raw31142Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw31142 raw31142Labels = mixedMoment B raw31142step0 raw31142step0Labels := by
      have hz : ∀ j, raw31142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31142step0 = (fun i j => raw31142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31142step0 raw31142; decide +kernel
      have hl : raw31142step0Labels = raw31142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31142 raw31142Labels permutation434 hz
    mixedMoment B raw31142step0 raw31142step0Labels = mixedMoment B raw31142step1 raw31142step1Labels := by
      have hz : ∀ j, raw31142step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31142step1 = (fun i j => raw31142step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31142step1 raw31142step0; decide +kernel
      have hl : raw31142step1Labels = raw31142step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31142step0 raw31142step0Labels permutation80 hz
    mixedMoment B raw31142step1 raw31142step1Labels = mixedMoment B raw31142step2 raw31142step2Labels := by
      have ha : raw31142step2 = (fun i j => raw31142step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31142step2 raw31142step1; decide +kernel
      have hl : raw31142step2Labels = raw31142step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31142step1 raw31142step1Labels permutation9 permutation7
    mixedMoment B raw31142step2 raw31142step2Labels = mixedMoment B raw31142step3 raw31142step3Labels := by
      have ha : raw31142step3 = -raw31142step2 := by apply Matrix.ext; change ∀ i j, raw31142step3 i j = -(raw31142step2 i j); unfold raw31142step3 raw31142step2; decide +kernel
      have hl : raw31142step3Labels = raw31142step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31142step3 raw31142step3Labels = mixedMoment B raw31142step4 raw31142step4Labels := by
      have ha : raw31142step4 = raw31142step3 := by apply Matrix.ext; unfold raw31142step4 raw31142step3; decide +kernel
      have hl : raw31142step3Labels = labelEmbedding10 ∘ raw31142step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31142step3 raw31142step3Labels raw31142step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw31143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31143 raw31143Labels = mixedMoment B node4701 node4701Labels := by
  calc
    mixedMoment B raw31143 raw31143Labels = mixedMoment B raw31143step0 raw31143step0Labels := by
      have hz : ∀ j, raw31143 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31143step0 = (fun i j => raw31143 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31143step0 raw31143; decide +kernel
      have hl : raw31143step0Labels = raw31143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31143 raw31143Labels permutation434 hz
    _ = mixedMoment B node4701 node4701Labels := by rfl

def raw31144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31144 raw31144Labels = mixedMoment B node4774 node4774Labels := by
  calc
    mixedMoment B raw31144 raw31144Labels = mixedMoment B raw31144step0 raw31144step0Labels := by
      have ha : raw31144step0 = (fun i j => raw31144 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31144step0 raw31144; decide +kernel
      have hl : raw31144step0Labels = raw31144Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31144 raw31144Labels permutation200 permutation2
    _ = mixedMoment B node4774 node4774Labels := by rfl

def raw31145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31145 raw31145Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw31145 raw31145Labels = mixedMoment B raw31145step0 raw31145step0Labels := by
      have hz : ∀ j, raw31145 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31145step0 = (fun i j => raw31145 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31145step0 raw31145; decide +kernel
      have hl : raw31145step0Labels = raw31145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31145 raw31145Labels permutation434 hz
    mixedMoment B raw31145step0 raw31145step0Labels = mixedMoment B raw31145step1 raw31145step1Labels := by
      have ha : raw31145step1 = (fun i j => raw31145step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31145step1 raw31145step0; decide +kernel
      have hl : raw31145step1Labels = raw31145step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31145step0 raw31145step0Labels permutation33 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw31146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31146 raw31146Labels = mixedMoment B node4701 node4701Labels := by
  calc
    mixedMoment B raw31146 raw31146Labels = mixedMoment B raw31146step0 raw31146step0Labels := by
      have hz : ∀ j, raw31146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31146step0 = (fun i j => raw31146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31146step0 raw31146; decide +kernel
      have hl : raw31146step0Labels = raw31146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31146 raw31146Labels permutation346 hz
    _ = mixedMoment B node4701 node4701Labels := by rfl

def raw31147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31147 raw31147Labels = mixedMoment B node4774 node4774Labels := by
  calc
    mixedMoment B raw31147 raw31147Labels = mixedMoment B raw31147step0 raw31147step0Labels := by
      have ha : raw31147step0 = (fun i j => raw31147 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31147step0 raw31147; decide +kernel
      have hl : raw31147step0Labels = raw31147Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31147 raw31147Labels permutation176 permutation2
    _ = mixedMoment B node4774 node4774Labels := by rfl

def raw31148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31148 raw31148Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw31148 raw31148Labels = mixedMoment B raw31148step0 raw31148step0Labels := by
      have hz : ∀ j, raw31148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31148step0 = (fun i j => raw31148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31148step0 raw31148; decide +kernel
      have hl : raw31148step0Labels = raw31148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31148 raw31148Labels permutation346 hz
    mixedMoment B raw31148step0 raw31148step0Labels = mixedMoment B raw31148step1 raw31148step1Labels := by
      have ha : raw31148step1 = (fun i j => raw31148step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31148step1 raw31148step0; decide +kernel
      have hl : raw31148step1Labels = raw31148step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31148step0 raw31148step0Labels permutation33 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw31149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31149step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31149 raw31149Labels = mixedMoment B node4705 node4705Labels := by
  calc
    mixedMoment B raw31149 raw31149Labels = mixedMoment B raw31149step0 raw31149step0Labels := by
      have hz : ∀ j, raw31149 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31149step0 = (fun i j => raw31149 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31149step0 raw31149; decide +kernel
      have hl : raw31149step0Labels = raw31149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31149 raw31149Labels permutation434 hz
    mixedMoment B raw31149step0 raw31149step0Labels = mixedMoment B raw31149step1 raw31149step1Labels := by
      have hz : ∀ j, raw31149step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31149step1 = (fun i j => raw31149step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31149step1 raw31149step0; decide +kernel
      have hl : raw31149step1Labels = raw31149step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31149step0 raw31149step0Labels permutation80 hz
    mixedMoment B raw31149step1 raw31149step1Labels = mixedMoment B raw31149step2 raw31149step2Labels := by
      have ha : raw31149step2 = (fun i j => raw31149step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31149step2 raw31149step1; decide +kernel
      have hl : raw31149step2Labels = raw31149step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31149step1 raw31149step1Labels permutation9 permutation2
    _ = mixedMoment B node4705 node4705Labels := by rfl

def raw31150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31150 raw31150Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw31150 raw31150Labels = mixedMoment B raw31150step0 raw31150step0Labels := by
      have hz : ∀ j, raw31150 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31150step0 = (fun i j => raw31150 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31150step0 raw31150; decide +kernel
      have hl : raw31150step0Labels = raw31150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31150 raw31150Labels permutation434 hz
    mixedMoment B raw31150step0 raw31150step0Labels = mixedMoment B raw31150step1 raw31150step1Labels := by
      have ha : raw31150step1 = (fun i j => raw31150step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31150step1 raw31150step0; decide +kernel
      have hl : raw31150step1Labels = raw31150step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31150step0 raw31150step0Labels permutation39 permutation2
    _ = mixedMoment B node4777 node4777Labels := by rfl

def raw31151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31151 raw31151Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw31151 raw31151Labels = mixedMoment B raw31151step0 raw31151step0Labels := by
      have hz : ∀ j, raw31151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31151step0 = (fun i j => raw31151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31151step0 raw31151; decide +kernel
      have hl : raw31151step0Labels = raw31151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31151 raw31151Labels permutation346 hz
    mixedMoment B raw31151step0 raw31151step0Labels = mixedMoment B raw31151step1 raw31151step1Labels := by
      have ha : raw31151step1 = (fun i j => raw31151step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31151step1 raw31151step0; decide +kernel
      have hl : raw31151step1Labels = raw31151step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31151step0 raw31151step0Labels permutation39 permutation2
    _ = mixedMoment B node4777 node4777Labels := by rfl

def raw31152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![3, -2, -1], ![1, 0, -1]]
def raw31152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31152 raw31152Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw31152 raw31152Labels = mixedMoment B raw31152step0 raw31152step0Labels := by
      have hz : ∀ j, raw31152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31152step0 = (fun i j => raw31152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31152step0 raw31152; decide +kernel
      have hl : raw31152step0Labels = raw31152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31152 raw31152Labels permutation434 hz
    mixedMoment B raw31152step0 raw31152step0Labels = mixedMoment B raw31152step1 raw31152step1Labels := by
      have hz : ∀ j, raw31152step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31152step1 = (fun i j => raw31152step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31152step1 raw31152step0; decide +kernel
      have hl : raw31152step1Labels = raw31152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31152step0 raw31152step0Labels permutation80 hz
    mixedMoment B raw31152step1 raw31152step1Labels = mixedMoment B raw31152step2 raw31152step2Labels := by
      have ha : raw31152step2 = (fun i j => raw31152step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31152step2 raw31152step1; decide +kernel
      have hl : raw31152step2Labels = raw31152step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31152step1 raw31152step1Labels permutation9 permutation2
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw31153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31153 raw31153Labels = mixedMoment B node4705 node4705Labels := by
  calc
    mixedMoment B raw31153 raw31153Labels = mixedMoment B raw31153step0 raw31153step0Labels := by
      have hz : ∀ j, raw31153 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31153step0 = (fun i j => raw31153 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31153step0 raw31153; decide +kernel
      have hl : raw31153step0Labels = raw31153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31153 raw31153Labels permutation434 hz
    mixedMoment B raw31153step0 raw31153step0Labels = mixedMoment B raw31153step1 raw31153step1Labels := by
      have hz : ∀ j, raw31153step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31153step1 = (fun i j => raw31153step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31153step1 raw31153step0; decide +kernel
      have hl : raw31153step1Labels = raw31153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31153step0 raw31153step0Labels permutation80 hz
    _ = mixedMoment B node4705 node4705Labels := by rfl

def raw31154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31154 raw31154Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw31154 raw31154Labels = mixedMoment B raw31154step0 raw31154step0Labels := by
      have hz : ∀ j, raw31154 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31154step0 = (fun i j => raw31154 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31154step0 raw31154; decide +kernel
      have hl : raw31154step0Labels = raw31154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31154 raw31154Labels permutation434 hz
    mixedMoment B raw31154step0 raw31154step0Labels = mixedMoment B raw31154step1 raw31154step1Labels := by
      have ha : raw31154step1 = (fun i j => raw31154step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31154step1 raw31154step0; decide +kernel
      have hl : raw31154step1Labels = raw31154step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31154step0 raw31154step0Labels permutation38 permutation2
    _ = mixedMoment B node4777 node4777Labels := by rfl

def raw31155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31155step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31155 raw31155Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw31155 raw31155Labels = mixedMoment B raw31155step0 raw31155step0Labels := by
      have hz : ∀ j, raw31155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31155step0 = (fun i j => raw31155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31155step0 raw31155; decide +kernel
      have hl : raw31155step0Labels = raw31155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31155 raw31155Labels permutation346 hz
    mixedMoment B raw31155step0 raw31155step0Labels = mixedMoment B raw31155step1 raw31155step1Labels := by
      have ha : raw31155step1 = (fun i j => raw31155step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31155step1 raw31155step0; decide +kernel
      have hl : raw31155step1Labels = raw31155step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31155step0 raw31155step0Labels permutation38 permutation2
    _ = mixedMoment B node4777 node4777Labels := by rfl

def raw31156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31156step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31156step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -2, 3]]
def raw31156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31156step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw31156step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31156 raw31156Labels = mixedMoment B node3118 node3118Labels := by
  calc
    mixedMoment B raw31156 raw31156Labels = mixedMoment B raw31156step0 raw31156step0Labels := by
      have hz : ∀ j, raw31156 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31156step0 = (fun i j => raw31156 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31156step0 raw31156; decide +kernel
      have hl : raw31156step0Labels = raw31156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31156 raw31156Labels permutation434 hz
    mixedMoment B raw31156step0 raw31156step0Labels = mixedMoment B raw31156step1 raw31156step1Labels := by
      have hz : ∀ j, raw31156step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31156step1 = (fun i j => raw31156step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31156step1 raw31156step0; decide +kernel
      have hl : raw31156step1Labels = raw31156step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31156step0 raw31156step0Labels permutation80 hz
    mixedMoment B raw31156step1 raw31156step1Labels = mixedMoment B raw31156step2 raw31156step2Labels := by
      have ha : raw31156step2 = (fun i j => raw31156step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31156step2 raw31156step1; decide +kernel
      have hl : raw31156step2Labels = raw31156step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31156step1 raw31156step1Labels permutation11 permutation6
    mixedMoment B raw31156step2 raw31156step2Labels = mixedMoment B raw31156step3 raw31156step3Labels := by
      have ha : raw31156step3 = -raw31156step2 := by apply Matrix.ext; change ∀ i j, raw31156step3 i j = -(raw31156step2 i j); unfold raw31156step3 raw31156step2; decide +kernel
      have hl : raw31156step3Labels = raw31156step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3118 node3118Labels := by rfl

def raw31157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31157step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw31157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw31157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31157 raw31157Labels = mixedMoment B node3108 node3108Labels := by
  calc
    mixedMoment B raw31157 raw31157Labels = mixedMoment B raw31157step0 raw31157step0Labels := by
      have hz : ∀ j, raw31157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31157step0 = (fun i j => raw31157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31157step0 raw31157; decide +kernel
      have hl : raw31157step0Labels = raw31157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31157 raw31157Labels permutation434 hz
    mixedMoment B raw31157step0 raw31157step0Labels = mixedMoment B raw31157step1 raw31157step1Labels := by
      have ha : raw31157step1 = (fun i j => raw31157step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31157step1 raw31157step0; decide +kernel
      have hl : raw31157step1Labels = raw31157step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31157step0 raw31157step0Labels permutation41 permutation6
    mixedMoment B raw31157step1 raw31157step1Labels = mixedMoment B raw31157step2 raw31157step2Labels := by
      have ha : raw31157step2 = -raw31157step1 := by apply Matrix.ext; change ∀ i j, raw31157step2 i j = -(raw31157step1 i j); unfold raw31157step2 raw31157step1; decide +kernel
      have hl : raw31157step2Labels = raw31157step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3108 node3108Labels := by rfl

def raw31158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw31158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw31158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31158 raw31158Labels = mixedMoment B node3108 node3108Labels := by
  calc
    mixedMoment B raw31158 raw31158Labels = mixedMoment B raw31158step0 raw31158step0Labels := by
      have hz : ∀ j, raw31158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31158step0 = (fun i j => raw31158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31158step0 raw31158; decide +kernel
      have hl : raw31158step0Labels = raw31158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31158 raw31158Labels permutation346 hz
    mixedMoment B raw31158step0 raw31158step0Labels = mixedMoment B raw31158step1 raw31158step1Labels := by
      have ha : raw31158step1 = (fun i j => raw31158step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31158step1 raw31158step0; decide +kernel
      have hl : raw31158step1Labels = raw31158step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31158step0 raw31158step0Labels permutation41 permutation6
    mixedMoment B raw31158step1 raw31158step1Labels = mixedMoment B raw31158step2 raw31158step2Labels := by
      have ha : raw31158step2 = -raw31158step1 := by apply Matrix.ext; change ∀ i j, raw31158step2 i j = -(raw31158step1 i j); unfold raw31158step2 raw31158step1; decide +kernel
      have hl : raw31158step2Labels = raw31158step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3108 node3108Labels := by rfl

def raw31159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31159step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31159step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw31159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31159step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw31159step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31159 raw31159Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw31159 raw31159Labels = mixedMoment B raw31159step0 raw31159step0Labels := by
      have hz : ∀ j, raw31159 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31159step0 = (fun i j => raw31159 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31159step0 raw31159; decide +kernel
      have hl : raw31159step0Labels = raw31159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31159 raw31159Labels permutation434 hz
    mixedMoment B raw31159step0 raw31159step0Labels = mixedMoment B raw31159step1 raw31159step1Labels := by
      have hz : ∀ j, raw31159step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31159step1 = (fun i j => raw31159step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31159step1 raw31159step0; decide +kernel
      have hl : raw31159step1Labels = raw31159step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31159step0 raw31159step0Labels permutation80 hz
    mixedMoment B raw31159step1 raw31159step1Labels = mixedMoment B raw31159step2 raw31159step2Labels := by
      have ha : raw31159step2 = (fun i j => raw31159step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31159step2 raw31159step1; decide +kernel
      have hl : raw31159step2Labels = raw31159step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31159step1 raw31159step1Labels permutation13 permutation6
    mixedMoment B raw31159step2 raw31159step2Labels = mixedMoment B raw31159step3 raw31159step3Labels := by
      have ha : raw31159step3 = -raw31159step2 := by apply Matrix.ext; change ∀ i j, raw31159step3 i j = -(raw31159step2 i j); unfold raw31159step3 raw31159step2; decide +kernel
      have hl : raw31159step3Labels = raw31159step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw31160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31160step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31160step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw31160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31160step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw31160step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31160 raw31160Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw31160 raw31160Labels = mixedMoment B raw31160step0 raw31160step0Labels := by
      have hz : ∀ j, raw31160 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31160step0 = (fun i j => raw31160 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31160step0 raw31160; decide +kernel
      have hl : raw31160step0Labels = raw31160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31160 raw31160Labels permutation434 hz
    mixedMoment B raw31160step0 raw31160step0Labels = mixedMoment B raw31160step1 raw31160step1Labels := by
      have hz : ∀ j, raw31160step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31160step1 = (fun i j => raw31160step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31160step1 raw31160step0; decide +kernel
      have hl : raw31160step1Labels = raw31160step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31160step0 raw31160step0Labels permutation80 hz
    mixedMoment B raw31160step1 raw31160step1Labels = mixedMoment B raw31160step2 raw31160step2Labels := by
      have ha : raw31160step2 = (fun i j => raw31160step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31160step2 raw31160step1; decide +kernel
      have hl : raw31160step2Labels = raw31160step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31160step1 raw31160step1Labels permutation11 permutation6
    mixedMoment B raw31160step2 raw31160step2Labels = mixedMoment B raw31160step3 raw31160step3Labels := by
      have ha : raw31160step3 = -raw31160step2 := by apply Matrix.ext; change ∀ i j, raw31160step3 i j = -(raw31160step2 i j); unfold raw31160step3 raw31160step2; decide +kernel
      have hl : raw31160step3Labels = raw31160step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw31161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31161 raw31161Labels = mixedMoment B node3132 node3132Labels := by
  calc
    mixedMoment B raw31161 raw31161Labels = mixedMoment B raw31161step0 raw31161step0Labels := by
      have hz : ∀ j, raw31161 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31161step0 = (fun i j => raw31161 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31161step0 raw31161; decide +kernel
      have hl : raw31161step0Labels = raw31161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31161 raw31161Labels permutation434 hz
    mixedMoment B raw31161step0 raw31161step0Labels = mixedMoment B raw31161step1 raw31161step1Labels := by
      have ha : raw31161step1 = (fun i j => raw31161step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31161step1 raw31161step0; decide +kernel
      have hl : raw31161step1Labels = raw31161step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31161step0 raw31161step0Labels permutation32 permutation3
    _ = mixedMoment B node3132 node3132Labels := by rfl

def raw31162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31162 raw31162Labels = mixedMoment B node3164 node3164Labels := by
  calc
    mixedMoment B raw31162 raw31162Labels = mixedMoment B raw31162step0 raw31162step0Labels := by
      have ha : raw31162step0 = (fun i j => raw31162 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31162step0 raw31162; decide +kernel
      have hl : raw31162step0Labels = raw31162Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31162 raw31162Labels permutation158 permutation3
    _ = mixedMoment B node3164 node3164Labels := by rfl

def raw31163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31163 raw31163Labels = mixedMoment B node3184 node3184Labels := by
  calc
    mixedMoment B raw31163 raw31163Labels = mixedMoment B raw31163step0 raw31163step0Labels := by
      have hz : ∀ j, raw31163 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31163step0 = (fun i j => raw31163 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31163step0 raw31163; decide +kernel
      have hl : raw31163step0Labels = raw31163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31163 raw31163Labels permutation434 hz
    mixedMoment B raw31163step0 raw31163step0Labels = mixedMoment B raw31163step1 raw31163step1Labels := by
      have ha : raw31163step1 = (fun i j => raw31163step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31163step1 raw31163step0; decide +kernel
      have hl : raw31163step1Labels = raw31163step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31163step0 raw31163step0Labels permutation34 permutation3
    _ = mixedMoment B node3184 node3184Labels := by rfl

def raw31164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31164 raw31164Labels = mixedMoment B node3184 node3184Labels := by
  calc
    mixedMoment B raw31164 raw31164Labels = mixedMoment B raw31164step0 raw31164step0Labels := by
      have hz : ∀ j, raw31164 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31164step0 = (fun i j => raw31164 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31164step0 raw31164; decide +kernel
      have hl : raw31164step0Labels = raw31164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31164 raw31164Labels permutation434 hz
    mixedMoment B raw31164step0 raw31164step0Labels = mixedMoment B raw31164step1 raw31164step1Labels := by
      have ha : raw31164step1 = (fun i j => raw31164step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31164step1 raw31164step0; decide +kernel
      have hl : raw31164step1Labels = raw31164step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31164step0 raw31164step0Labels permutation36 permutation3
    _ = mixedMoment B node3184 node3184Labels := by rfl

def raw31165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31165 raw31165Labels = mixedMoment B node3132 node3132Labels := by
  calc
    mixedMoment B raw31165 raw31165Labels = mixedMoment B raw31165step0 raw31165step0Labels := by
      have hz : ∀ j, raw31165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31165step0 = (fun i j => raw31165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31165step0 raw31165; decide +kernel
      have hl : raw31165step0Labels = raw31165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31165 raw31165Labels permutation346 hz
    mixedMoment B raw31165step0 raw31165step0Labels = mixedMoment B raw31165step1 raw31165step1Labels := by
      have ha : raw31165step1 = (fun i j => raw31165step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31165step1 raw31165step0; decide +kernel
      have hl : raw31165step1Labels = raw31165step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31165step0 raw31165step0Labels permutation32 permutation3
    _ = mixedMoment B node3132 node3132Labels := by rfl

def raw31166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31166 raw31166Labels = mixedMoment B node3164 node3164Labels := by
  calc
    mixedMoment B raw31166 raw31166Labels = mixedMoment B raw31166step0 raw31166step0Labels := by
      have ha : raw31166step0 = (fun i j => raw31166 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31166step0 raw31166; decide +kernel
      have hl : raw31166step0Labels = raw31166Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31166 raw31166Labels permutation152 permutation3
    _ = mixedMoment B node3164 node3164Labels := by rfl

def raw31167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31167 raw31167Labels = mixedMoment B node3184 node3184Labels := by
  calc
    mixedMoment B raw31167 raw31167Labels = mixedMoment B raw31167step0 raw31167step0Labels := by
      have hz : ∀ j, raw31167 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31167step0 = (fun i j => raw31167 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31167step0 raw31167; decide +kernel
      have hl : raw31167step0Labels = raw31167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31167 raw31167Labels permutation346 hz
    mixedMoment B raw31167step0 raw31167step0Labels = mixedMoment B raw31167step1 raw31167step1Labels := by
      have ha : raw31167step1 = (fun i j => raw31167step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31167step1 raw31167step0; decide +kernel
      have hl : raw31167step1Labels = raw31167step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31167step0 raw31167step0Labels permutation34 permutation3
    _ = mixedMoment B node3184 node3184Labels := by rfl

def raw31168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31168 raw31168Labels = mixedMoment B node3184 node3184Labels := by
  calc
    mixedMoment B raw31168 raw31168Labels = mixedMoment B raw31168step0 raw31168step0Labels := by
      have hz : ∀ j, raw31168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31168step0 = (fun i j => raw31168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31168step0 raw31168; decide +kernel
      have hl : raw31168step0Labels = raw31168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31168 raw31168Labels permutation346 hz
    mixedMoment B raw31168step0 raw31168step0Labels = mixedMoment B raw31168step1 raw31168step1Labels := by
      have ha : raw31168step1 = (fun i j => raw31168step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31168step1 raw31168step0; decide +kernel
      have hl : raw31168step1Labels = raw31168step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31168step0 raw31168step0Labels permutation36 permutation3
    _ = mixedMoment B node3184 node3184Labels := by rfl

def raw31169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31169step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw31169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31169step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw31169step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31169 raw31169Labels = mixedMoment B node2346 node2346Labels := by
  calc
    mixedMoment B raw31169 raw31169Labels = mixedMoment B raw31169step0 raw31169step0Labels := by
      have hz : ∀ j, raw31169 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31169step0 = (fun i j => raw31169 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31169step0 raw31169; decide +kernel
      have hl : raw31169step0Labels = raw31169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31169 raw31169Labels permutation434 hz
    mixedMoment B raw31169step0 raw31169step0Labels = mixedMoment B raw31169step1 raw31169step1Labels := by
      have hz : ∀ j, raw31169step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31169step1 = (fun i j => raw31169step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31169step1 raw31169step0; decide +kernel
      have hl : raw31169step1Labels = raw31169step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31169step0 raw31169step0Labels permutation80 hz
    mixedMoment B raw31169step1 raw31169step1Labels = mixedMoment B raw31169step2 raw31169step2Labels := by
      have ha : raw31169step2 = (fun i j => raw31169step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31169step2 raw31169step1; decide +kernel
      have hl : raw31169step2Labels = raw31169step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31169step1 raw31169step1Labels permutation25 permutation3
    mixedMoment B raw31169step2 raw31169step2Labels = mixedMoment B raw31169step3 raw31169step3Labels := by
      have ha : raw31169step3 = -raw31169step2 := by apply Matrix.ext; change ∀ i j, raw31169step3 i j = -(raw31169step2 i j); unfold raw31169step3 raw31169step2; decide +kernel
      have hl : raw31169step3Labels = raw31169step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2346 node2346Labels := by rfl

def raw31170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31170 raw31170Labels = mixedMoment B node2340 node2340Labels := by
  calc
    mixedMoment B raw31170 raw31170Labels = mixedMoment B raw31170step0 raw31170step0Labels := by
      have hz : ∀ j, raw31170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31170step0 = (fun i j => raw31170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31170step0 raw31170; decide +kernel
      have hl : raw31170step0Labels = raw31170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31170 raw31170Labels permutation434 hz
    mixedMoment B raw31170step0 raw31170step0Labels = mixedMoment B raw31170step1 raw31170step1Labels := by
      have ha : raw31170step1 = (fun i j => raw31170step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31170step1 raw31170step0; decide +kernel
      have hl : raw31170step1Labels = raw31170step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31170step0 raw31170step0Labels permutation127 permutation3
    mixedMoment B raw31170step1 raw31170step1Labels = mixedMoment B raw31170step2 raw31170step2Labels := by
      have ha : raw31170step2 = -raw31170step1 := by apply Matrix.ext; change ∀ i j, raw31170step2 i j = -(raw31170step1 i j); unfold raw31170step2 raw31170step1; decide +kernel
      have hl : raw31170step2Labels = raw31170step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2340 node2340Labels := by rfl

def raw31171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31171 raw31171Labels = mixedMoment B node2340 node2340Labels := by
  calc
    mixedMoment B raw31171 raw31171Labels = mixedMoment B raw31171step0 raw31171step0Labels := by
      have hz : ∀ j, raw31171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31171step0 = (fun i j => raw31171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31171step0 raw31171; decide +kernel
      have hl : raw31171step0Labels = raw31171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31171 raw31171Labels permutation346 hz
    mixedMoment B raw31171step0 raw31171step0Labels = mixedMoment B raw31171step1 raw31171step1Labels := by
      have ha : raw31171step1 = (fun i j => raw31171step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31171step1 raw31171step0; decide +kernel
      have hl : raw31171step1Labels = raw31171step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31171step0 raw31171step0Labels permutation127 permutation3
    mixedMoment B raw31171step1 raw31171step1Labels = mixedMoment B raw31171step2 raw31171step2Labels := by
      have ha : raw31171step2 = -raw31171step1 := by apply Matrix.ext; change ∀ i j, raw31171step2 i j = -(raw31171step1 i j); unfold raw31171step2 raw31171step1; decide +kernel
      have hl : raw31171step2Labels = raw31171step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2340 node2340Labels := by rfl

def raw31172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![3, -2, -1], ![1, 0, -1]]
def raw31172step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, -1, 2], ![-3, 3, 0]]
def raw31172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31172step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw31172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31172 raw31172Labels = mixedMoment B node2602 node2602Labels := by
  calc
    mixedMoment B raw31172 raw31172Labels = mixedMoment B raw31172step0 raw31172step0Labels := by
      have hz : ∀ j, raw31172 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31172step0 = (fun i j => raw31172 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31172step0 raw31172; decide +kernel
      have hl : raw31172step0Labels = raw31172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31172 raw31172Labels permutation434 hz
    mixedMoment B raw31172step0 raw31172step0Labels = mixedMoment B raw31172step1 raw31172step1Labels := by
      have hz : ∀ j, raw31172step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31172step1 = (fun i j => raw31172step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31172step1 raw31172step0; decide +kernel
      have hl : raw31172step1Labels = raw31172step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31172step0 raw31172step0Labels permutation80 hz
    mixedMoment B raw31172step1 raw31172step1Labels = mixedMoment B raw31172step2 raw31172step2Labels := by
      have ha : raw31172step2 = (fun i j => raw31172step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31172step2 raw31172step1; decide +kernel
      have hl : raw31172step2Labels = raw31172step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31172step1 raw31172step1Labels permutation25 permutation3
    mixedMoment B raw31172step2 raw31172step2Labels = mixedMoment B raw31172step3 raw31172step3Labels := by
      have ha : raw31172step3 = -raw31172step2 := by apply Matrix.ext; change ∀ i j, raw31172step3 i j = -(raw31172step2 i j); unfold raw31172step3 raw31172step2; decide +kernel
      have hl : raw31172step3Labels = raw31172step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2602 node2602Labels := by rfl

def raw31173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31173step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw31173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31173step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw31173step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31173 raw31173Labels = mixedMoment B node2346 node2346Labels := by
  calc
    mixedMoment B raw31173 raw31173Labels = mixedMoment B raw31173step0 raw31173step0Labels := by
      have hz : ∀ j, raw31173 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31173step0 = (fun i j => raw31173 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31173step0 raw31173; decide +kernel
      have hl : raw31173step0Labels = raw31173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31173 raw31173Labels permutation434 hz
    mixedMoment B raw31173step0 raw31173step0Labels = mixedMoment B raw31173step1 raw31173step1Labels := by
      have hz : ∀ j, raw31173step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31173step1 = (fun i j => raw31173step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31173step1 raw31173step0; decide +kernel
      have hl : raw31173step1Labels = raw31173step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31173step0 raw31173step0Labels permutation80 hz
    mixedMoment B raw31173step1 raw31173step1Labels = mixedMoment B raw31173step2 raw31173step2Labels := by
      have ha : raw31173step2 = (fun i j => raw31173step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31173step2 raw31173step1; decide +kernel
      have hl : raw31173step2Labels = raw31173step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31173step1 raw31173step1Labels permutation31 permutation3
    mixedMoment B raw31173step2 raw31173step2Labels = mixedMoment B raw31173step3 raw31173step3Labels := by
      have ha : raw31173step3 = -raw31173step2 := by apply Matrix.ext; change ∀ i j, raw31173step3 i j = -(raw31173step2 i j); unfold raw31173step3 raw31173step2; decide +kernel
      have hl : raw31173step3Labels = raw31173step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2346 node2346Labels := by rfl

def raw31174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31174 raw31174Labels = mixedMoment B node2340 node2340Labels := by
  calc
    mixedMoment B raw31174 raw31174Labels = mixedMoment B raw31174step0 raw31174step0Labels := by
      have hz : ∀ j, raw31174 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31174step0 = (fun i j => raw31174 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31174step0 raw31174; decide +kernel
      have hl : raw31174step0Labels = raw31174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31174 raw31174Labels permutation434 hz
    mixedMoment B raw31174step0 raw31174step0Labels = mixedMoment B raw31174step1 raw31174step1Labels := by
      have ha : raw31174step1 = (fun i j => raw31174step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31174step1 raw31174step0; decide +kernel
      have hl : raw31174step1Labels = raw31174step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31174step0 raw31174step0Labels permutation151 permutation3
    mixedMoment B raw31174step1 raw31174step1Labels = mixedMoment B raw31174step2 raw31174step2Labels := by
      have ha : raw31174step2 = -raw31174step1 := by apply Matrix.ext; change ∀ i j, raw31174step2 i j = -(raw31174step1 i j); unfold raw31174step2 raw31174step1; decide +kernel
      have hl : raw31174step2Labels = raw31174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2340 node2340Labels := by rfl

def raw31175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31175 raw31175Labels = mixedMoment B node2340 node2340Labels := by
  calc
    mixedMoment B raw31175 raw31175Labels = mixedMoment B raw31175step0 raw31175step0Labels := by
      have hz : ∀ j, raw31175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31175step0 = (fun i j => raw31175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31175step0 raw31175; decide +kernel
      have hl : raw31175step0Labels = raw31175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31175 raw31175Labels permutation346 hz
    mixedMoment B raw31175step0 raw31175step0Labels = mixedMoment B raw31175step1 raw31175step1Labels := by
      have ha : raw31175step1 = (fun i j => raw31175step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31175step1 raw31175step0; decide +kernel
      have hl : raw31175step1Labels = raw31175step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31175step0 raw31175step0Labels permutation151 permutation3
    mixedMoment B raw31175step1 raw31175step1Labels = mixedMoment B raw31175step2 raw31175step2Labels := by
      have ha : raw31175step2 = -raw31175step1 := by apply Matrix.ext; change ∀ i j, raw31175step2 i j = -(raw31175step1 i j); unfold raw31175step2 raw31175step1; decide +kernel
      have hl : raw31175step2Labels = raw31175step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2340 node2340Labels := by rfl

def raw31176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31176step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31176step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw31176step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31176step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31176step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31176step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31176step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31176 raw31176Labels = mixedMoment B node2779 node2779Labels := by
  calc
    mixedMoment B raw31176 raw31176Labels = mixedMoment B raw31176step0 raw31176step0Labels := by
      have hz : ∀ j, raw31176 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31176step0 = (fun i j => raw31176 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31176step0 raw31176; decide +kernel
      have hl : raw31176step0Labels = raw31176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31176 raw31176Labels permutation434 hz
    mixedMoment B raw31176step0 raw31176step0Labels = mixedMoment B raw31176step1 raw31176step1Labels := by
      have hz : ∀ j, raw31176step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31176step1 = (fun i j => raw31176step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31176step1 raw31176step0; decide +kernel
      have hl : raw31176step1Labels = raw31176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31176step0 raw31176step0Labels permutation80 hz
    mixedMoment B raw31176step1 raw31176step1Labels = mixedMoment B raw31176step2 raw31176step2Labels := by
      have ha : raw31176step2 = (fun i j => raw31176step1 (permutation14 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31176step2 raw31176step1; decide +kernel
      have hl : raw31176step2Labels = raw31176step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31176step1 raw31176step1Labels permutation14 permutation5
    mixedMoment B raw31176step2 raw31176step2Labels = mixedMoment B raw31176step3 raw31176step3Labels := by
      have ha : raw31176step3 = -raw31176step2 := by apply Matrix.ext; change ∀ i j, raw31176step3 i j = -(raw31176step2 i j); unfold raw31176step3 raw31176step2; decide +kernel
      have hl : raw31176step3Labels = raw31176step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31176step3 raw31176step3Labels = mixedMoment B raw31176step4 raw31176step4Labels := by
      have ha : raw31176step4 = raw31176step3 := by apply Matrix.ext; unfold raw31176step4 raw31176step3; decide +kernel
      have hl : raw31176step3Labels = labelEmbedding1 ∘ raw31176step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31176step3 raw31176step3Labels raw31176step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2779 node2779Labels := by rfl

def raw31177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31177step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31177step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31177step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31177 raw31177Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw31177 raw31177Labels = mixedMoment B raw31177step0 raw31177step0Labels := by
      have hz : ∀ j, raw31177 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31177step0 = (fun i j => raw31177 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31177step0 raw31177; decide +kernel
      have hl : raw31177step0Labels = raw31177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31177 raw31177Labels permutation434 hz
    mixedMoment B raw31177step0 raw31177step0Labels = mixedMoment B raw31177step1 raw31177step1Labels := by
      have ha : raw31177step1 = (fun i j => raw31177step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31177step1 raw31177step0; decide +kernel
      have hl : raw31177step1Labels = raw31177step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31177step0 raw31177step0Labels permutation38 permutation7
    mixedMoment B raw31177step1 raw31177step1Labels = mixedMoment B raw31177step2 raw31177step2Labels := by
      have ha : raw31177step2 = -raw31177step1 := by apply Matrix.ext; change ∀ i j, raw31177step2 i j = -(raw31177step1 i j); unfold raw31177step2 raw31177step1; decide +kernel
      have hl : raw31177step2Labels = raw31177step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31177step2 raw31177step2Labels = mixedMoment B raw31177step3 raw31177step3Labels := by
      have ha : raw31177step3 = raw31177step2 := by apply Matrix.ext; unfold raw31177step3 raw31177step2; decide +kernel
      have hl : raw31177step2Labels = labelEmbedding1 ∘ raw31177step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31177step2 raw31177step2Labels raw31177step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

def raw31178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31178step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31178step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31178step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31178step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31178 raw31178Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw31178 raw31178Labels = mixedMoment B raw31178step0 raw31178step0Labels := by
      have hz : ∀ j, raw31178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31178step0 = (fun i j => raw31178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31178step0 raw31178; decide +kernel
      have hl : raw31178step0Labels = raw31178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31178 raw31178Labels permutation346 hz
    mixedMoment B raw31178step0 raw31178step0Labels = mixedMoment B raw31178step1 raw31178step1Labels := by
      have ha : raw31178step1 = (fun i j => raw31178step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31178step1 raw31178step0; decide +kernel
      have hl : raw31178step1Labels = raw31178step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31178step0 raw31178step0Labels permutation38 permutation7
    mixedMoment B raw31178step1 raw31178step1Labels = mixedMoment B raw31178step2 raw31178step2Labels := by
      have ha : raw31178step2 = -raw31178step1 := by apply Matrix.ext; change ∀ i j, raw31178step2 i j = -(raw31178step1 i j); unfold raw31178step2 raw31178step1; decide +kernel
      have hl : raw31178step2Labels = raw31178step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31178step2 raw31178step2Labels = mixedMoment B raw31178step3 raw31178step3Labels := by
      have ha : raw31178step3 = raw31178step2 := by apply Matrix.ext; unfold raw31178step3 raw31178step2; decide +kernel
      have hl : raw31178step2Labels = labelEmbedding1 ∘ raw31178step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31178step2 raw31178step2Labels raw31178step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

def raw31179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31179step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31179step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31179step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31179step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31179step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31179step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31179step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31179step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31179 raw31179Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw31179 raw31179Labels = mixedMoment B raw31179step0 raw31179step0Labels := by
      have hz : ∀ j, raw31179 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31179step0 = (fun i j => raw31179 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31179step0 raw31179; decide +kernel
      have hl : raw31179step0Labels = raw31179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31179 raw31179Labels permutation434 hz
    mixedMoment B raw31179step0 raw31179step0Labels = mixedMoment B raw31179step1 raw31179step1Labels := by
      have hz : ∀ j, raw31179step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31179step1 = (fun i j => raw31179step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31179step1 raw31179step0; decide +kernel
      have hl : raw31179step1Labels = raw31179step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31179step0 raw31179step0Labels permutation80 hz
    mixedMoment B raw31179step1 raw31179step1Labels = mixedMoment B raw31179step2 raw31179step2Labels := by
      have ha : raw31179step2 = (fun i j => raw31179step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31179step2 raw31179step1; decide +kernel
      have hl : raw31179step2Labels = raw31179step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31179step1 raw31179step1Labels permutation9 permutation7
    mixedMoment B raw31179step2 raw31179step2Labels = mixedMoment B raw31179step3 raw31179step3Labels := by
      have ha : raw31179step3 = -raw31179step2 := by apply Matrix.ext; change ∀ i j, raw31179step3 i j = -(raw31179step2 i j); unfold raw31179step3 raw31179step2; decide +kernel
      have hl : raw31179step3Labels = raw31179step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31179step3 raw31179step3Labels = mixedMoment B raw31179step4 raw31179step4Labels := by
      have ha : raw31179step4 = raw31179step3 := by apply Matrix.ext; unfold raw31179step4 raw31179step3; decide +kernel
      have hl : raw31179step3Labels = labelEmbedding1 ∘ raw31179step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31179step3 raw31179step3Labels raw31179step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw31180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw31180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31180step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31180 raw31180Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw31180 raw31180Labels = mixedMoment B raw31180step0 raw31180step0Labels := by
      have hz : ∀ j, raw31180 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31180step0 = (fun i j => raw31180 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31180step0 raw31180; decide +kernel
      have hl : raw31180step0Labels = raw31180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31180 raw31180Labels permutation434 hz
    mixedMoment B raw31180step0 raw31180step0Labels = mixedMoment B raw31180step1 raw31180step1Labels := by
      have ha : raw31180step1 = (fun i j => raw31180step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31180step1 raw31180step0; decide +kernel
      have hl : raw31180step1Labels = raw31180step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31180step0 raw31180step0Labels permutation38 permutation7
    mixedMoment B raw31180step1 raw31180step1Labels = mixedMoment B raw31180step2 raw31180step2Labels := by
      have ha : raw31180step2 = -raw31180step1 := by apply Matrix.ext; change ∀ i j, raw31180step2 i j = -(raw31180step1 i j); unfold raw31180step2 raw31180step1; decide +kernel
      have hl : raw31180step2Labels = raw31180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31180step2 raw31180step2Labels = mixedMoment B raw31180step3 raw31180step3Labels := by
      have ha : raw31180step3 = raw31180step2 := by apply Matrix.ext; unfold raw31180step3 raw31180step2; decide +kernel
      have hl : raw31180step2Labels = labelEmbedding1 ∘ raw31180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31180step2 raw31180step2Labels raw31180step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2257 node2257Labels := by rfl

def raw31181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31181 raw31181Labels = mixedMoment B node2199 node2199Labels := by
  calc
    mixedMoment B raw31181 raw31181Labels = mixedMoment B raw31181step0 raw31181step0Labels := by
      have ha : raw31181step0 = (fun i j => raw31181 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31181step0 raw31181; decide +kernel
      have hl : raw31181step0Labels = raw31181Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31181 raw31181Labels permutation206 permutation7
    mixedMoment B raw31181step0 raw31181step0Labels = mixedMoment B raw31181step1 raw31181step1Labels := by
      have ha : raw31181step1 = -raw31181step0 := by apply Matrix.ext; change ∀ i j, raw31181step1 i j = -(raw31181step0 i j); unfold raw31181step1 raw31181step0; decide +kernel
      have hl : raw31181step1Labels = raw31181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31181step1 raw31181step1Labels = mixedMoment B raw31181step2 raw31181step2Labels := by
      have ha : raw31181step2 = raw31181step1 := by apply Matrix.ext; unfold raw31181step2 raw31181step1; decide +kernel
      have hl : raw31181step1Labels = labelEmbedding1 ∘ raw31181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31181step1 raw31181step1Labels raw31181step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2199 node2199Labels := by rfl

def raw31182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31182step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31182step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31182step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31182step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31182 raw31182Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw31182 raw31182Labels = mixedMoment B raw31182step0 raw31182step0Labels := by
      have hz : ∀ j, raw31182 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31182step0 = (fun i j => raw31182 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31182step0 raw31182; decide +kernel
      have hl : raw31182step0Labels = raw31182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31182 raw31182Labels permutation434 hz
    mixedMoment B raw31182step0 raw31182step0Labels = mixedMoment B raw31182step1 raw31182step1Labels := by
      have ha : raw31182step1 = (fun i j => raw31182step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31182step1 raw31182step0; decide +kernel
      have hl : raw31182step1Labels = raw31182step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31182step0 raw31182step0Labels permutation39 permutation7
    mixedMoment B raw31182step1 raw31182step1Labels = mixedMoment B raw31182step2 raw31182step2Labels := by
      have ha : raw31182step2 = -raw31182step1 := by apply Matrix.ext; change ∀ i j, raw31182step2 i j = -(raw31182step1 i j); unfold raw31182step2 raw31182step1; decide +kernel
      have hl : raw31182step2Labels = raw31182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31182step2 raw31182step2Labels = mixedMoment B raw31182step3 raw31182step3Labels := by
      have ha : raw31182step3 = raw31182step2 := by apply Matrix.ext; unfold raw31182step3 raw31182step2; decide +kernel
      have hl : raw31182step2Labels = labelEmbedding1 ∘ raw31182step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31182step2 raw31182step2Labels raw31182step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw31183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31183step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw31183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31183step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31183step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw31183step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31183 raw31183Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw31183 raw31183Labels = mixedMoment B raw31183step0 raw31183step0Labels := by
      have hz : ∀ j, raw31183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31183step0 = (fun i j => raw31183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31183step0 raw31183; decide +kernel
      have hl : raw31183step0Labels = raw31183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31183 raw31183Labels permutation346 hz
    mixedMoment B raw31183step0 raw31183step0Labels = mixedMoment B raw31183step1 raw31183step1Labels := by
      have ha : raw31183step1 = (fun i j => raw31183step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31183step1 raw31183step0; decide +kernel
      have hl : raw31183step1Labels = raw31183step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31183step0 raw31183step0Labels permutation38 permutation7
    mixedMoment B raw31183step1 raw31183step1Labels = mixedMoment B raw31183step2 raw31183step2Labels := by
      have ha : raw31183step2 = -raw31183step1 := by apply Matrix.ext; change ∀ i j, raw31183step2 i j = -(raw31183step1 i j); unfold raw31183step2 raw31183step1; decide +kernel
      have hl : raw31183step2Labels = raw31183step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31183step2 raw31183step2Labels = mixedMoment B raw31183step3 raw31183step3Labels := by
      have ha : raw31183step3 = raw31183step2 := by apply Matrix.ext; unfold raw31183step3 raw31183step2; decide +kernel
      have hl : raw31183step2Labels = labelEmbedding1 ∘ raw31183step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31183step2 raw31183step2Labels raw31183step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2257 node2257Labels := by rfl

def raw31184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31184step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31184 raw31184Labels = mixedMoment B node2199 node2199Labels := by
  calc
    mixedMoment B raw31184 raw31184Labels = mixedMoment B raw31184step0 raw31184step0Labels := by
      have ha : raw31184step0 = (fun i j => raw31184 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31184step0 raw31184; decide +kernel
      have hl : raw31184step0Labels = raw31184Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31184 raw31184Labels permutation182 permutation7
    mixedMoment B raw31184step0 raw31184step0Labels = mixedMoment B raw31184step1 raw31184step1Labels := by
      have ha : raw31184step1 = -raw31184step0 := by apply Matrix.ext; change ∀ i j, raw31184step1 i j = -(raw31184step0 i j); unfold raw31184step1 raw31184step0; decide +kernel
      have hl : raw31184step1Labels = raw31184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31184step1 raw31184step1Labels = mixedMoment B raw31184step2 raw31184step2Labels := by
      have ha : raw31184step2 = raw31184step1 := by apply Matrix.ext; unfold raw31184step2 raw31184step1; decide +kernel
      have hl : raw31184step1Labels = labelEmbedding1 ∘ raw31184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31184step1 raw31184step1Labels raw31184step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2199 node2199Labels := by rfl

def raw31185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31185step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31185step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw31185step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31185 raw31185Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw31185 raw31185Labels = mixedMoment B raw31185step0 raw31185step0Labels := by
      have hz : ∀ j, raw31185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31185step0 = (fun i j => raw31185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31185step0 raw31185; decide +kernel
      have hl : raw31185step0Labels = raw31185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31185 raw31185Labels permutation346 hz
    mixedMoment B raw31185step0 raw31185step0Labels = mixedMoment B raw31185step1 raw31185step1Labels := by
      have ha : raw31185step1 = (fun i j => raw31185step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31185step1 raw31185step0; decide +kernel
      have hl : raw31185step1Labels = raw31185step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31185step0 raw31185step0Labels permutation39 permutation7
    mixedMoment B raw31185step1 raw31185step1Labels = mixedMoment B raw31185step2 raw31185step2Labels := by
      have ha : raw31185step2 = -raw31185step1 := by apply Matrix.ext; change ∀ i j, raw31185step2 i j = -(raw31185step1 i j); unfold raw31185step2 raw31185step1; decide +kernel
      have hl : raw31185step2Labels = raw31185step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31185step2 raw31185step2Labels = mixedMoment B raw31185step3 raw31185step3Labels := by
      have ha : raw31185step3 = raw31185step2 := by apply Matrix.ext; unfold raw31185step3 raw31185step2; decide +kernel
      have hl : raw31185step2Labels = labelEmbedding1 ∘ raw31185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31185step2 raw31185step2Labels raw31185step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw31186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31186step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![-1, -1, 2], ![-1, -2, 3]]
def raw31186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31186step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw31186step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31186step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw31186step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31186 raw31186Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw31186 raw31186Labels = mixedMoment B raw31186step0 raw31186step0Labels := by
      have hz : ∀ j, raw31186 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31186step0 = (fun i j => raw31186 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31186step0 raw31186; decide +kernel
      have hl : raw31186step0Labels = raw31186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31186 raw31186Labels permutation434 hz
    mixedMoment B raw31186step0 raw31186step0Labels = mixedMoment B raw31186step1 raw31186step1Labels := by
      have hz : ∀ j, raw31186step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31186step1 = (fun i j => raw31186step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31186step1 raw31186step0; decide +kernel
      have hl : raw31186step1Labels = raw31186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31186step0 raw31186step0Labels permutation80 hz
    mixedMoment B raw31186step1 raw31186step1Labels = mixedMoment B raw31186step2 raw31186step2Labels := by
      have ha : raw31186step2 = (fun i j => raw31186step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31186step2 raw31186step1; decide +kernel
      have hl : raw31186step2Labels = raw31186step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31186step1 raw31186step1Labels permutation9 permutation7
    mixedMoment B raw31186step2 raw31186step2Labels = mixedMoment B raw31186step3 raw31186step3Labels := by
      have ha : raw31186step3 = -raw31186step2 := by apply Matrix.ext; change ∀ i j, raw31186step3 i j = -(raw31186step2 i j); unfold raw31186step3 raw31186step2; decide +kernel
      have hl : raw31186step3Labels = raw31186step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31186step3 raw31186step3Labels = mixedMoment B raw31186step4 raw31186step4Labels := by
      have ha : raw31186step4 = raw31186step3 := by apply Matrix.ext; unfold raw31186step4 raw31186step3; decide +kernel
      have hl : raw31186step3Labels = labelEmbedding1 ∘ raw31186step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31186step3 raw31186step3Labels raw31186step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2286 node2286Labels := by rfl

def raw31187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31187step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw31187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31187step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31187step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31187step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31187 raw31187Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw31187 raw31187Labels = mixedMoment B raw31187step0 raw31187step0Labels := by
      have hz : ∀ j, raw31187 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31187step0 = (fun i j => raw31187 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31187step0 raw31187; decide +kernel
      have hl : raw31187step0Labels = raw31187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31187 raw31187Labels permutation434 hz
    mixedMoment B raw31187step0 raw31187step0Labels = mixedMoment B raw31187step1 raw31187step1Labels := by
      have ha : raw31187step1 = (fun i j => raw31187step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31187step1 raw31187step0; decide +kernel
      have hl : raw31187step1Labels = raw31187step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31187step0 raw31187step0Labels permutation39 permutation7
    mixedMoment B raw31187step1 raw31187step1Labels = mixedMoment B raw31187step2 raw31187step2Labels := by
      have ha : raw31187step2 = -raw31187step1 := by apply Matrix.ext; change ∀ i j, raw31187step2 i j = -(raw31187step1 i j); unfold raw31187step2 raw31187step1; decide +kernel
      have hl : raw31187step2Labels = raw31187step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31187step2 raw31187step2Labels = mixedMoment B raw31187step3 raw31187step3Labels := by
      have ha : raw31187step3 = raw31187step2 := by apply Matrix.ext; unfold raw31187step3 raw31187step2; decide +kernel
      have hl : raw31187step2Labels = labelEmbedding1 ∘ raw31187step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31187step2 raw31187step2Labels raw31187step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

def raw31188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw31188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31188step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31188 raw31188Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw31188 raw31188Labels = mixedMoment B raw31188step0 raw31188step0Labels := by
      have hz : ∀ j, raw31188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31188step0 = (fun i j => raw31188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31188step0 raw31188; decide +kernel
      have hl : raw31188step0Labels = raw31188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31188 raw31188Labels permutation346 hz
    mixedMoment B raw31188step0 raw31188step0Labels = mixedMoment B raw31188step1 raw31188step1Labels := by
      have ha : raw31188step1 = (fun i j => raw31188step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31188step1 raw31188step0; decide +kernel
      have hl : raw31188step1Labels = raw31188step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31188step0 raw31188step0Labels permutation39 permutation7
    mixedMoment B raw31188step1 raw31188step1Labels = mixedMoment B raw31188step2 raw31188step2Labels := by
      have ha : raw31188step2 = -raw31188step1 := by apply Matrix.ext; change ∀ i j, raw31188step2 i j = -(raw31188step1 i j); unfold raw31188step2 raw31188step1; decide +kernel
      have hl : raw31188step2Labels = raw31188step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31188step2 raw31188step2Labels = mixedMoment B raw31188step3 raw31188step3Labels := by
      have ha : raw31188step3 = raw31188step2 := by apply Matrix.ext; unfold raw31188step3 raw31188step2; decide +kernel
      have hl : raw31188step2Labels = labelEmbedding1 ∘ raw31188step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31188step2 raw31188step2Labels raw31188step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

def raw31189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31189step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![3, -2, -1], ![1, 0, -1]]
def raw31189step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31189step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw31189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31189step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw31189step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31189step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw31189step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31189 raw31189Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw31189 raw31189Labels = mixedMoment B raw31189step0 raw31189step0Labels := by
      have hz : ∀ j, raw31189 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31189step0 = (fun i j => raw31189 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31189step0 raw31189; decide +kernel
      have hl : raw31189step0Labels = raw31189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31189 raw31189Labels permutation434 hz
    mixedMoment B raw31189step0 raw31189step0Labels = mixedMoment B raw31189step1 raw31189step1Labels := by
      have hz : ∀ j, raw31189step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31189step1 = (fun i j => raw31189step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31189step1 raw31189step0; decide +kernel
      have hl : raw31189step1Labels = raw31189step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31189step0 raw31189step0Labels permutation80 hz
    mixedMoment B raw31189step1 raw31189step1Labels = mixedMoment B raw31189step2 raw31189step2Labels := by
      have ha : raw31189step2 = (fun i j => raw31189step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31189step2 raw31189step1; decide +kernel
      have hl : raw31189step2Labels = raw31189step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31189step1 raw31189step1Labels permutation9 permutation7
    mixedMoment B raw31189step2 raw31189step2Labels = mixedMoment B raw31189step3 raw31189step3Labels := by
      have ha : raw31189step3 = -raw31189step2 := by apply Matrix.ext; change ∀ i j, raw31189step3 i j = -(raw31189step2 i j); unfold raw31189step3 raw31189step2; decide +kernel
      have hl : raw31189step3Labels = raw31189step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31189step3 raw31189step3Labels = mixedMoment B raw31189step4 raw31189step4Labels := by
      have ha : raw31189step4 = raw31189step3 := by apply Matrix.ext; unfold raw31189step4 raw31189step3; decide +kernel
      have hl : raw31189step3Labels = labelEmbedding1 ∘ raw31189step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31189step3 raw31189step3Labels raw31189step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw31190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31190step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31190step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31190step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![-1, -1, 2], ![-1, -2, 3]]
def raw31190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31190step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw31190step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31190step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw31190step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31190 raw31190Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw31190 raw31190Labels = mixedMoment B raw31190step0 raw31190step0Labels := by
      have hz : ∀ j, raw31190 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31190step0 = (fun i j => raw31190 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31190step0 raw31190; decide +kernel
      have hl : raw31190step0Labels = raw31190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31190 raw31190Labels permutation434 hz
    mixedMoment B raw31190step0 raw31190step0Labels = mixedMoment B raw31190step1 raw31190step1Labels := by
      have hz : ∀ j, raw31190step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31190step1 = (fun i j => raw31190step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31190step1 raw31190step0; decide +kernel
      have hl : raw31190step1Labels = raw31190step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31190step0 raw31190step0Labels permutation80 hz
    mixedMoment B raw31190step1 raw31190step1Labels = mixedMoment B raw31190step2 raw31190step2Labels := by
      have ha : raw31190step2 = (fun i j => raw31190step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31190step2 raw31190step1; decide +kernel
      have hl : raw31190step2Labels = raw31190step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31190step1 raw31190step1Labels permutation8 permutation7
    mixedMoment B raw31190step2 raw31190step2Labels = mixedMoment B raw31190step3 raw31190step3Labels := by
      have ha : raw31190step3 = -raw31190step2 := by apply Matrix.ext; change ∀ i j, raw31190step3 i j = -(raw31190step2 i j); unfold raw31190step3 raw31190step2; decide +kernel
      have hl : raw31190step3Labels = raw31190step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31190step3 raw31190step3Labels = mixedMoment B raw31190step4 raw31190step4Labels := by
      have ha : raw31190step4 = raw31190step3 := by apply Matrix.ext; unfold raw31190step4 raw31190step3; decide +kernel
      have hl : raw31190step3Labels = labelEmbedding1 ∘ raw31190step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31190step3 raw31190step3Labels raw31190step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2286 node2286Labels := by rfl

def raw31191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw31191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31191step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31191step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31191step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31191 raw31191Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw31191 raw31191Labels = mixedMoment B raw31191step0 raw31191step0Labels := by
      have hz : ∀ j, raw31191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31191step0 = (fun i j => raw31191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31191step0 raw31191; decide +kernel
      have hl : raw31191step0Labels = raw31191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31191 raw31191Labels permutation434 hz
    mixedMoment B raw31191step0 raw31191step0Labels = mixedMoment B raw31191step1 raw31191step1Labels := by
      have ha : raw31191step1 = (fun i j => raw31191step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31191step1 raw31191step0; decide +kernel
      have hl : raw31191step1Labels = raw31191step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31191step0 raw31191step0Labels permutation38 permutation7
    mixedMoment B raw31191step1 raw31191step1Labels = mixedMoment B raw31191step2 raw31191step2Labels := by
      have ha : raw31191step2 = -raw31191step1 := by apply Matrix.ext; change ∀ i j, raw31191step2 i j = -(raw31191step1 i j); unfold raw31191step2 raw31191step1; decide +kernel
      have hl : raw31191step2Labels = raw31191step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31191step2 raw31191step2Labels = mixedMoment B raw31191step3 raw31191step3Labels := by
      have ha : raw31191step3 = raw31191step2 := by apply Matrix.ext; unfold raw31191step3 raw31191step2; decide +kernel
      have hl : raw31191step2Labels = labelEmbedding1 ∘ raw31191step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31191step2 raw31191step2Labels raw31191step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

def raw31192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw31192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31192step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31192step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31192step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31192 raw31192Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw31192 raw31192Labels = mixedMoment B raw31192step0 raw31192step0Labels := by
      have hz : ∀ j, raw31192 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31192step0 = (fun i j => raw31192 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31192step0 raw31192; decide +kernel
      have hl : raw31192step0Labels = raw31192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31192 raw31192Labels permutation346 hz
    mixedMoment B raw31192step0 raw31192step0Labels = mixedMoment B raw31192step1 raw31192step1Labels := by
      have ha : raw31192step1 = (fun i j => raw31192step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31192step1 raw31192step0; decide +kernel
      have hl : raw31192step1Labels = raw31192step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31192step0 raw31192step0Labels permutation38 permutation7
    mixedMoment B raw31192step1 raw31192step1Labels = mixedMoment B raw31192step2 raw31192step2Labels := by
      have ha : raw31192step2 = -raw31192step1 := by apply Matrix.ext; change ∀ i j, raw31192step2 i j = -(raw31192step1 i j); unfold raw31192step2 raw31192step1; decide +kernel
      have hl : raw31192step2Labels = raw31192step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31192step2 raw31192step2Labels = mixedMoment B raw31192step3 raw31192step3Labels := by
      have ha : raw31192step3 = raw31192step2 := by apply Matrix.ext; unfold raw31192step3 raw31192step2; decide +kernel
      have hl : raw31192step2Labels = labelEmbedding1 ∘ raw31192step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31192step2 raw31192step2Labels raw31192step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

def raw31193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31193step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31193step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -2, 3]]
def raw31193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31193step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw31193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31193 raw31193Labels = mixedMoment B node3118 node3118Labels := by
  calc
    mixedMoment B raw31193 raw31193Labels = mixedMoment B raw31193step0 raw31193step0Labels := by
      have hz : ∀ j, raw31193 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31193step0 = (fun i j => raw31193 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31193step0 raw31193; decide +kernel
      have hl : raw31193step0Labels = raw31193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31193 raw31193Labels permutation434 hz
    mixedMoment B raw31193step0 raw31193step0Labels = mixedMoment B raw31193step1 raw31193step1Labels := by
      have hz : ∀ j, raw31193step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31193step1 = (fun i j => raw31193step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31193step1 raw31193step0; decide +kernel
      have hl : raw31193step1Labels = raw31193step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31193step0 raw31193step0Labels permutation80 hz
    mixedMoment B raw31193step1 raw31193step1Labels = mixedMoment B raw31193step2 raw31193step2Labels := by
      have ha : raw31193step2 = (fun i j => raw31193step1 (permutation17 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31193step2 raw31193step1; decide +kernel
      have hl : raw31193step2Labels = raw31193step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31193step1 raw31193step1Labels permutation17 permutation4
    mixedMoment B raw31193step2 raw31193step2Labels = mixedMoment B raw31193step3 raw31193step3Labels := by
      have ha : raw31193step3 = -raw31193step2 := by apply Matrix.ext; change ∀ i j, raw31193step3 i j = -(raw31193step2 i j); unfold raw31193step3 raw31193step2; decide +kernel
      have hl : raw31193step3Labels = raw31193step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3118 node3118Labels := by rfl

def raw31194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31194 raw31194Labels = mixedMoment B node1827 node1827Labels := by
  calc
    mixedMoment B raw31194 raw31194Labels = mixedMoment B raw31194step0 raw31194step0Labels := by
      have hz : ∀ j, raw31194 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31194step0 = (fun i j => raw31194 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31194step0 raw31194; decide +kernel
      have hl : raw31194step0Labels = raw31194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31194 raw31194Labels permutation434 hz
    _ = mixedMoment B node1827 node1827Labels := by rfl

def raw31195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31195 raw31195Labels = mixedMoment B node1827 node1827Labels := by
  calc
    mixedMoment B raw31195 raw31195Labels = mixedMoment B raw31195step0 raw31195step0Labels := by
      have hz : ∀ j, raw31195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31195step0 = (fun i j => raw31195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31195step0 raw31195; decide +kernel
      have hl : raw31195step0Labels = raw31195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31195 raw31195Labels permutation346 hz
    _ = mixedMoment B node1827 node1827Labels := by rfl

def raw31196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31196step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31196 raw31196Labels = mixedMoment B node1831 node1831Labels := by
  calc
    mixedMoment B raw31196 raw31196Labels = mixedMoment B raw31196step0 raw31196step0Labels := by
      have hz : ∀ j, raw31196 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31196step0 = (fun i j => raw31196 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31196step0 raw31196; decide +kernel
      have hl : raw31196step0Labels = raw31196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31196 raw31196Labels permutation434 hz
    mixedMoment B raw31196step0 raw31196step0Labels = mixedMoment B raw31196step1 raw31196step1Labels := by
      have hz : ∀ j, raw31196step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31196step1 = (fun i j => raw31196step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31196step1 raw31196step0; decide +kernel
      have hl : raw31196step1Labels = raw31196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31196step0 raw31196step0Labels permutation80 hz
    mixedMoment B raw31196step1 raw31196step1Labels = mixedMoment B raw31196step2 raw31196step2Labels := by
      have ha : raw31196step2 = (fun i j => raw31196step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31196step2 raw31196step1; decide +kernel
      have hl : raw31196step2Labels = raw31196step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31196step1 raw31196step1Labels permutation9 permutation2
    _ = mixedMoment B node1831 node1831Labels := by rfl

def raw31197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31197 raw31197Labels = mixedMoment B node1831 node1831Labels := by
  calc
    mixedMoment B raw31197 raw31197Labels = mixedMoment B raw31197step0 raw31197step0Labels := by
      have hz : ∀ j, raw31197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31197step0 = (fun i j => raw31197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31197step0 raw31197; decide +kernel
      have hl : raw31197step0Labels = raw31197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31197 raw31197Labels permutation434 hz
    mixedMoment B raw31197step0 raw31197step0Labels = mixedMoment B raw31197step1 raw31197step1Labels := by
      have hz : ∀ j, raw31197step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31197step1 = (fun i j => raw31197step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31197step1 raw31197step0; decide +kernel
      have hl : raw31197step1Labels = raw31197step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31197step0 raw31197step0Labels permutation80 hz
    _ = mixedMoment B node1831 node1831Labels := by rfl

def raw31198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31198 raw31198Labels = mixedMoment B node1975 node1975Labels := by
  calc
    mixedMoment B raw31198 raw31198Labels = mixedMoment B raw31198step0 raw31198step0Labels := by
      have ha : raw31198step0 = (fun i j => raw31198 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31198step0 raw31198; decide +kernel
      have hl : raw31198step0Labels = raw31198Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31198 raw31198Labels permutation200 permutation2
    _ = mixedMoment B node1975 node1975Labels := by rfl

def raw31199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31199step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31199 raw31199Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw31199 raw31199Labels = mixedMoment B raw31199step0 raw31199step0Labels := by
      have hz : ∀ j, raw31199 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31199step0 = (fun i j => raw31199 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31199step0 raw31199; decide +kernel
      have hl : raw31199step0Labels = raw31199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31199 raw31199Labels permutation434 hz
    mixedMoment B raw31199step0 raw31199step0Labels = mixedMoment B raw31199step1 raw31199step1Labels := by
      have ha : raw31199step1 = (fun i j => raw31199step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31199step1 raw31199step0; decide +kernel
      have hl : raw31199step1Labels = raw31199step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31199step0 raw31199step0Labels permutation33 permutation2
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw31200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31200step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31200step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31200 raw31200Labels = mixedMoment B node4239 node4239Labels := by
  calc
    mixedMoment B raw31200 raw31200Labels = mixedMoment B raw31200step0 raw31200step0Labels := by
      have hz : ∀ j, raw31200 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31200step0 = (fun i j => raw31200 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31200step0 raw31200; decide +kernel
      have hl : raw31200step0Labels = raw31200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31200 raw31200Labels permutation434 hz
    mixedMoment B raw31200step0 raw31200step0Labels = mixedMoment B raw31200step1 raw31200step1Labels := by
      have ha : raw31200step1 = (fun i j => raw31200step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31200step1 raw31200step0; decide +kernel
      have hl : raw31200step1Labels = raw31200step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31200step0 raw31200step0Labels permutation32 permutation3
    mixedMoment B raw31200step1 raw31200step1Labels = mixedMoment B raw31200step2 raw31200step2Labels := by
      have ha : raw31200step2 = raw31200step1 := by apply Matrix.ext; unfold raw31200step2 raw31200step1; decide +kernel
      have hl : raw31200step1Labels = labelEmbedding6 ∘ raw31200step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31200step1 raw31200step1Labels raw31200step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4239 node4239Labels := by rfl

def raw31201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31201step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31201step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31201 raw31201Labels = mixedMoment B node4689 node4689Labels := by
  calc
    mixedMoment B raw31201 raw31201Labels = mixedMoment B raw31201step0 raw31201step0Labels := by
      have hz : ∀ j, raw31201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31201step0 = (fun i j => raw31201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31201step0 raw31201; decide +kernel
      have hl : raw31201step0Labels = raw31201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31201 raw31201Labels permutation434 hz
    mixedMoment B raw31201step0 raw31201step0Labels = mixedMoment B raw31201step1 raw31201step1Labels := by
      have ha : raw31201step1 = (fun i j => raw31201step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31201step1 raw31201step0; decide +kernel
      have hl : raw31201step1Labels = raw31201step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31201step0 raw31201step0Labels permutation32 permutation3
    mixedMoment B raw31201step1 raw31201step1Labels = mixedMoment B raw31201step2 raw31201step2Labels := by
      have ha : raw31201step2 = raw31201step1 := by apply Matrix.ext; unfold raw31201step2 raw31201step1; decide +kernel
      have hl : raw31201step1Labels = labelEmbedding6 ∘ raw31201step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31201step1 raw31201step1Labels raw31201step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4689 node4689Labels := by rfl

def raw31202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31202step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31202 raw31202Labels = mixedMoment B node4725 node4725Labels := by
  calc
    mixedMoment B raw31202 raw31202Labels = mixedMoment B raw31202step0 raw31202step0Labels := by
      have ha : raw31202step0 = (fun i j => raw31202 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31202step0 raw31202; decide +kernel
      have hl : raw31202step0Labels = raw31202Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31202 raw31202Labels permutation200 permutation3
    mixedMoment B raw31202step0 raw31202step0Labels = mixedMoment B raw31202step1 raw31202step1Labels := by
      have ha : raw31202step1 = raw31202step0 := by apply Matrix.ext; unfold raw31202step1 raw31202step0; decide +kernel
      have hl : raw31202step0Labels = labelEmbedding6 ∘ raw31202step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31202step0 raw31202step0Labels raw31202step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4725 node4725Labels := by rfl

def raw31203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31203step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31203step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31203 raw31203Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw31203 raw31203Labels = mixedMoment B raw31203step0 raw31203step0Labels := by
      have hz : ∀ j, raw31203 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31203step0 = (fun i j => raw31203 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31203step0 raw31203; decide +kernel
      have hl : raw31203step0Labels = raw31203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31203 raw31203Labels permutation434 hz
    mixedMoment B raw31203step0 raw31203step0Labels = mixedMoment B raw31203step1 raw31203step1Labels := by
      have ha : raw31203step1 = (fun i j => raw31203step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31203step1 raw31203step0; decide +kernel
      have hl : raw31203step1Labels = raw31203step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31203step0 raw31203step0Labels permutation36 permutation3
    mixedMoment B raw31203step1 raw31203step1Labels = mixedMoment B raw31203step2 raw31203step2Labels := by
      have ha : raw31203step2 = raw31203step1 := by apply Matrix.ext; unfold raw31203step2 raw31203step1; decide +kernel
      have hl : raw31203step1Labels = labelEmbedding6 ∘ raw31203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31203step1 raw31203step1Labels raw31203step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw31204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31204step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31204step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31204 raw31204Labels = mixedMoment B node4239 node4239Labels := by
  calc
    mixedMoment B raw31204 raw31204Labels = mixedMoment B raw31204step0 raw31204step0Labels := by
      have hz : ∀ j, raw31204 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31204step0 = (fun i j => raw31204 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31204step0 raw31204; decide +kernel
      have hl : raw31204step0Labels = raw31204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31204 raw31204Labels permutation346 hz
    mixedMoment B raw31204step0 raw31204step0Labels = mixedMoment B raw31204step1 raw31204step1Labels := by
      have ha : raw31204step1 = (fun i j => raw31204step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31204step1 raw31204step0; decide +kernel
      have hl : raw31204step1Labels = raw31204step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31204step0 raw31204step0Labels permutation32 permutation3
    mixedMoment B raw31204step1 raw31204step1Labels = mixedMoment B raw31204step2 raw31204step2Labels := by
      have ha : raw31204step2 = raw31204step1 := by apply Matrix.ext; unfold raw31204step2 raw31204step1; decide +kernel
      have hl : raw31204step1Labels = labelEmbedding6 ∘ raw31204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31204step1 raw31204step1Labels raw31204step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4239 node4239Labels := by rfl

def raw31205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31205step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31205step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31205 raw31205Labels = mixedMoment B node4689 node4689Labels := by
  calc
    mixedMoment B raw31205 raw31205Labels = mixedMoment B raw31205step0 raw31205step0Labels := by
      have hz : ∀ j, raw31205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31205step0 = (fun i j => raw31205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31205step0 raw31205; decide +kernel
      have hl : raw31205step0Labels = raw31205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31205 raw31205Labels permutation346 hz
    mixedMoment B raw31205step0 raw31205step0Labels = mixedMoment B raw31205step1 raw31205step1Labels := by
      have ha : raw31205step1 = (fun i j => raw31205step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31205step1 raw31205step0; decide +kernel
      have hl : raw31205step1Labels = raw31205step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31205step0 raw31205step0Labels permutation32 permutation3
    mixedMoment B raw31205step1 raw31205step1Labels = mixedMoment B raw31205step2 raw31205step2Labels := by
      have ha : raw31205step2 = raw31205step1 := by apply Matrix.ext; unfold raw31205step2 raw31205step1; decide +kernel
      have hl : raw31205step1Labels = labelEmbedding6 ∘ raw31205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31205step1 raw31205step1Labels raw31205step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4689 node4689Labels := by rfl

def raw31206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31206step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31206 raw31206Labels = mixedMoment B node4725 node4725Labels := by
  calc
    mixedMoment B raw31206 raw31206Labels = mixedMoment B raw31206step0 raw31206step0Labels := by
      have ha : raw31206step0 = (fun i j => raw31206 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31206step0 raw31206; decide +kernel
      have hl : raw31206step0Labels = raw31206Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31206 raw31206Labels permutation176 permutation3
    mixedMoment B raw31206step0 raw31206step0Labels = mixedMoment B raw31206step1 raw31206step1Labels := by
      have ha : raw31206step1 = raw31206step0 := by apply Matrix.ext; unfold raw31206step1 raw31206step0; decide +kernel
      have hl : raw31206step0Labels = labelEmbedding6 ∘ raw31206step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31206step0 raw31206step0Labels raw31206step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4725 node4725Labels := by rfl

def raw31207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31207step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31207step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31207 raw31207Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw31207 raw31207Labels = mixedMoment B raw31207step0 raw31207step0Labels := by
      have hz : ∀ j, raw31207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31207step0 = (fun i j => raw31207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31207step0 raw31207; decide +kernel
      have hl : raw31207step0Labels = raw31207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31207 raw31207Labels permutation346 hz
    mixedMoment B raw31207step0 raw31207step0Labels = mixedMoment B raw31207step1 raw31207step1Labels := by
      have ha : raw31207step1 = (fun i j => raw31207step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31207step1 raw31207step0; decide +kernel
      have hl : raw31207step1Labels = raw31207step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31207step0 raw31207step0Labels permutation36 permutation3
    mixedMoment B raw31207step1 raw31207step1Labels = mixedMoment B raw31207step2 raw31207step2Labels := by
      have ha : raw31207step2 = raw31207step1 := by apply Matrix.ext; unfold raw31207step2 raw31207step1; decide +kernel
      have hl : raw31207step1Labels = labelEmbedding6 ∘ raw31207step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31207step1 raw31207step1Labels raw31207step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw31208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![3, -2, -1], ![2, -1, -1]]
def raw31208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31208step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31208step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31208 raw31208Labels = mixedMoment B node4242 node4242Labels := by
  calc
    mixedMoment B raw31208 raw31208Labels = mixedMoment B raw31208step0 raw31208step0Labels := by
      have hz : ∀ j, raw31208 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31208step0 = (fun i j => raw31208 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31208step0 raw31208; decide +kernel
      have hl : raw31208step0Labels = raw31208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31208 raw31208Labels permutation434 hz
    mixedMoment B raw31208step0 raw31208step0Labels = mixedMoment B raw31208step1 raw31208step1Labels := by
      have hz : ∀ j, raw31208step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31208step1 = (fun i j => raw31208step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31208step1 raw31208step0; decide +kernel
      have hl : raw31208step1Labels = raw31208step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31208step0 raw31208step0Labels permutation80 hz
    mixedMoment B raw31208step1 raw31208step1Labels = mixedMoment B raw31208step2 raw31208step2Labels := by
      have ha : raw31208step2 = (fun i j => raw31208step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31208step2 raw31208step1; decide +kernel
      have hl : raw31208step2Labels = raw31208step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31208step1 raw31208step1Labels permutation9 permutation3
    mixedMoment B raw31208step2 raw31208step2Labels = mixedMoment B raw31208step3 raw31208step3Labels := by
      have ha : raw31208step3 = raw31208step2 := by apply Matrix.ext; unfold raw31208step3 raw31208step2; decide +kernel
      have hl : raw31208step2Labels = labelEmbedding6 ∘ raw31208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31208step2 raw31208step2Labels raw31208step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4242 node4242Labels := by rfl

def raw31209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![3, -2, -1], ![2, -1, -1]]
def raw31209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31209step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31209step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31209step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31209step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31209 raw31209Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw31209 raw31209Labels = mixedMoment B raw31209step0 raw31209step0Labels := by
      have hz : ∀ j, raw31209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31209step0 = (fun i j => raw31209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31209step0 raw31209; decide +kernel
      have hl : raw31209step0Labels = raw31209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31209 raw31209Labels permutation434 hz
    mixedMoment B raw31209step0 raw31209step0Labels = mixedMoment B raw31209step1 raw31209step1Labels := by
      have hz : ∀ j, raw31209step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31209step1 = (fun i j => raw31209step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31209step1 raw31209step0; decide +kernel
      have hl : raw31209step1Labels = raw31209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31209step0 raw31209step0Labels permutation80 hz
    mixedMoment B raw31209step1 raw31209step1Labels = mixedMoment B raw31209step2 raw31209step2Labels := by
      have ha : raw31209step2 = (fun i j => raw31209step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31209step2 raw31209step1; decide +kernel
      have hl : raw31209step2Labels = raw31209step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31209step1 raw31209step1Labels permutation9 permutation3
    mixedMoment B raw31209step2 raw31209step2Labels = mixedMoment B raw31209step3 raw31209step3Labels := by
      have ha : raw31209step3 = raw31209step2 := by apply Matrix.ext; unfold raw31209step3 raw31209step2; decide +kernel
      have hl : raw31209step2Labels = labelEmbedding6 ∘ raw31209step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31209step2 raw31209step2Labels raw31209step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4692 node4692Labels := by rfl

def raw31210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31210step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31210 raw31210Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw31210 raw31210Labels = mixedMoment B raw31210step0 raw31210step0Labels := by
      have hz : ∀ j, raw31210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31210step0 = (fun i j => raw31210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31210step0 raw31210; decide +kernel
      have hl : raw31210step0Labels = raw31210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31210 raw31210Labels permutation434 hz
    mixedMoment B raw31210step0 raw31210step0Labels = mixedMoment B raw31210step1 raw31210step1Labels := by
      have ha : raw31210step1 = (fun i j => raw31210step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31210step1 raw31210step0; decide +kernel
      have hl : raw31210step1Labels = raw31210step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31210step0 raw31210step0Labels permutation39 permutation3
    mixedMoment B raw31210step1 raw31210step1Labels = mixedMoment B raw31210step2 raw31210step2Labels := by
      have ha : raw31210step2 = raw31210step1 := by apply Matrix.ext; unfold raw31210step2 raw31210step1; decide +kernel
      have hl : raw31210step1Labels = labelEmbedding6 ∘ raw31210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31210step1 raw31210step1Labels raw31210step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4726 node4726Labels := by rfl

def raw31211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31211step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31211step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31211 raw31211Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw31211 raw31211Labels = mixedMoment B raw31211step0 raw31211step0Labels := by
      have hz : ∀ j, raw31211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31211step0 = (fun i j => raw31211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31211step0 raw31211; decide +kernel
      have hl : raw31211step0Labels = raw31211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31211 raw31211Labels permutation346 hz
    mixedMoment B raw31211step0 raw31211step0Labels = mixedMoment B raw31211step1 raw31211step1Labels := by
      have ha : raw31211step1 = (fun i j => raw31211step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31211step1 raw31211step0; decide +kernel
      have hl : raw31211step1Labels = raw31211step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31211step0 raw31211step0Labels permutation39 permutation3
    mixedMoment B raw31211step1 raw31211step1Labels = mixedMoment B raw31211step2 raw31211step2Labels := by
      have ha : raw31211step2 = raw31211step1 := by apply Matrix.ext; unfold raw31211step2 raw31211step1; decide +kernel
      have hl : raw31211step1Labels = labelEmbedding6 ∘ raw31211step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31211step1 raw31211step1Labels raw31211step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4726 node4726Labels := by rfl

def raw31212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![3, -2, -1], ![1, 0, -1]]
def raw31212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31212step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31212step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31212step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31212step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31212 raw31212Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw31212 raw31212Labels = mixedMoment B raw31212step0 raw31212step0Labels := by
      have hz : ∀ j, raw31212 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31212step0 = (fun i j => raw31212 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31212step0 raw31212; decide +kernel
      have hl : raw31212step0Labels = raw31212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31212 raw31212Labels permutation434 hz
    mixedMoment B raw31212step0 raw31212step0Labels = mixedMoment B raw31212step1 raw31212step1Labels := by
      have hz : ∀ j, raw31212step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31212step1 = (fun i j => raw31212step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31212step1 raw31212step0; decide +kernel
      have hl : raw31212step1Labels = raw31212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31212step0 raw31212step0Labels permutation80 hz
    mixedMoment B raw31212step1 raw31212step1Labels = mixedMoment B raw31212step2 raw31212step2Labels := by
      have ha : raw31212step2 = (fun i j => raw31212step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31212step2 raw31212step1; decide +kernel
      have hl : raw31212step2Labels = raw31212step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31212step1 raw31212step1Labels permutation9 permutation3
    mixedMoment B raw31212step2 raw31212step2Labels = mixedMoment B raw31212step3 raw31212step3Labels := by
      have ha : raw31212step3 = raw31212step2 := by apply Matrix.ext; unfold raw31212step3 raw31212step2; decide +kernel
      have hl : raw31212step2Labels = labelEmbedding6 ∘ raw31212step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31212step2 raw31212step2Labels raw31212step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw31213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -1, -1], ![3, -2, -1]]
def raw31213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31213step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31213step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31213 raw31213Labels = mixedMoment B node4242 node4242Labels := by
  calc
    mixedMoment B raw31213 raw31213Labels = mixedMoment B raw31213step0 raw31213step0Labels := by
      have hz : ∀ j, raw31213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31213step0 = (fun i j => raw31213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31213step0 raw31213; decide +kernel
      have hl : raw31213step0Labels = raw31213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31213 raw31213Labels permutation434 hz
    mixedMoment B raw31213step0 raw31213step0Labels = mixedMoment B raw31213step1 raw31213step1Labels := by
      have hz : ∀ j, raw31213step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31213step1 = (fun i j => raw31213step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31213step1 raw31213step0; decide +kernel
      have hl : raw31213step1Labels = raw31213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31213step0 raw31213step0Labels permutation80 hz
    mixedMoment B raw31213step1 raw31213step1Labels = mixedMoment B raw31213step2 raw31213step2Labels := by
      have ha : raw31213step2 = (fun i j => raw31213step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31213step2 raw31213step1; decide +kernel
      have hl : raw31213step2Labels = raw31213step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31213step1 raw31213step1Labels permutation8 permutation3
    mixedMoment B raw31213step2 raw31213step2Labels = mixedMoment B raw31213step3 raw31213step3Labels := by
      have ha : raw31213step3 = raw31213step2 := by apply Matrix.ext; unfold raw31213step3 raw31213step2; decide +kernel
      have hl : raw31213step2Labels = labelEmbedding6 ∘ raw31213step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31213step2 raw31213step2Labels raw31213step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4242 node4242Labels := by rfl

def raw31214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![3, -2, -1]]
def raw31214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31214step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31214step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31214step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31214 raw31214Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw31214 raw31214Labels = mixedMoment B raw31214step0 raw31214step0Labels := by
      have hz : ∀ j, raw31214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31214step0 = (fun i j => raw31214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31214step0 raw31214; decide +kernel
      have hl : raw31214step0Labels = raw31214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31214 raw31214Labels permutation434 hz
    mixedMoment B raw31214step0 raw31214step0Labels = mixedMoment B raw31214step1 raw31214step1Labels := by
      have hz : ∀ j, raw31214step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31214step1 = (fun i j => raw31214step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31214step1 raw31214step0; decide +kernel
      have hl : raw31214step1Labels = raw31214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31214step0 raw31214step0Labels permutation80 hz
    mixedMoment B raw31214step1 raw31214step1Labels = mixedMoment B raw31214step2 raw31214step2Labels := by
      have ha : raw31214step2 = (fun i j => raw31214step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31214step2 raw31214step1; decide +kernel
      have hl : raw31214step2Labels = raw31214step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31214step1 raw31214step1Labels permutation8 permutation3
    mixedMoment B raw31214step2 raw31214step2Labels = mixedMoment B raw31214step3 raw31214step3Labels := by
      have ha : raw31214step3 = raw31214step2 := by apply Matrix.ext; unfold raw31214step3 raw31214step2; decide +kernel
      have hl : raw31214step2Labels = labelEmbedding6 ∘ raw31214step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31214step2 raw31214step2Labels raw31214step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4692 node4692Labels := by rfl

def raw31215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31215step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31215 raw31215Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw31215 raw31215Labels = mixedMoment B raw31215step0 raw31215step0Labels := by
      have hz : ∀ j, raw31215 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31215step0 = (fun i j => raw31215 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31215step0 raw31215; decide +kernel
      have hl : raw31215step0Labels = raw31215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31215 raw31215Labels permutation434 hz
    mixedMoment B raw31215step0 raw31215step0Labels = mixedMoment B raw31215step1 raw31215step1Labels := by
      have ha : raw31215step1 = (fun i j => raw31215step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31215step1 raw31215step0; decide +kernel
      have hl : raw31215step1Labels = raw31215step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31215step0 raw31215step0Labels permutation38 permutation3
    mixedMoment B raw31215step1 raw31215step1Labels = mixedMoment B raw31215step2 raw31215step2Labels := by
      have ha : raw31215step2 = raw31215step1 := by apply Matrix.ext; unfold raw31215step2 raw31215step1; decide +kernel
      have hl : raw31215step1Labels = labelEmbedding6 ∘ raw31215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31215step1 raw31215step1Labels raw31215step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4726 node4726Labels := by rfl

def raw31216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31216step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31216step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31216 raw31216Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw31216 raw31216Labels = mixedMoment B raw31216step0 raw31216step0Labels := by
      have hz : ∀ j, raw31216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31216step0 = (fun i j => raw31216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31216step0 raw31216; decide +kernel
      have hl : raw31216step0Labels = raw31216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31216 raw31216Labels permutation346 hz
    mixedMoment B raw31216step0 raw31216step0Labels = mixedMoment B raw31216step1 raw31216step1Labels := by
      have ha : raw31216step1 = (fun i j => raw31216step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31216step1 raw31216step0; decide +kernel
      have hl : raw31216step1Labels = raw31216step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31216step0 raw31216step0Labels permutation38 permutation3
    mixedMoment B raw31216step1 raw31216step1Labels = mixedMoment B raw31216step2 raw31216step2Labels := by
      have ha : raw31216step2 = raw31216step1 := by apply Matrix.ext; unfold raw31216step2 raw31216step1; decide +kernel
      have hl : raw31216step1Labels = labelEmbedding6 ∘ raw31216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31216step1 raw31216step1Labels raw31216step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4726 node4726Labels := by rfl

def raw31217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31217Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31217step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31217 raw31217Labels = mixedMoment B node739 node739Labels := by
  calc
    mixedMoment B raw31217 raw31217Labels = mixedMoment B raw31217step0 raw31217step0Labels := by
      have hz : ∀ j, raw31217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31217step0 = (fun i j => raw31217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31217step0 raw31217; decide +kernel
      have hl : raw31217step0Labels = raw31217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31217 raw31217Labels permutation434 hz
    mixedMoment B raw31217step0 raw31217step0Labels = mixedMoment B raw31217step1 raw31217step1Labels := by
      have ha : raw31217step1 = (fun i j => raw31217step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31217step1 raw31217step0; decide +kernel
      have hl : raw31217step1Labels = raw31217step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31217step0 raw31217step0Labels permutation32 permutation3
    _ = mixedMoment B node739 node739Labels := by rfl

def raw31218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31218Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31218step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31218 raw31218Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw31218 raw31218Labels = mixedMoment B raw31218step0 raw31218step0Labels := by
      have hz : ∀ j, raw31218 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31218step0 = (fun i j => raw31218 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31218step0 raw31218; decide +kernel
      have hl : raw31218step0Labels = raw31218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31218 raw31218Labels permutation434 hz
    mixedMoment B raw31218step0 raw31218step0Labels = mixedMoment B raw31218step1 raw31218step1Labels := by
      have ha : raw31218step1 = (fun i j => raw31218step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31218step1 raw31218step0; decide +kernel
      have hl : raw31218step1Labels = raw31218step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31218step0 raw31218step0Labels permutation32 permutation3
    _ = mixedMoment B node1815 node1815Labels := by rfl

def raw31219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31219Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31219 raw31219Labels = mixedMoment B node1879 node1879Labels := by
  calc
    mixedMoment B raw31219 raw31219Labels = mixedMoment B raw31219step0 raw31219step0Labels := by
      have ha : raw31219step0 = (fun i j => raw31219 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31219step0 raw31219; decide +kernel
      have hl : raw31219step0Labels = raw31219Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31219 raw31219Labels permutation200 permutation3
    _ = mixedMoment B node1879 node1879Labels := by rfl

def raw31220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31220Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31220step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31220 raw31220Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw31220 raw31220Labels = mixedMoment B raw31220step0 raw31220step0Labels := by
      have hz : ∀ j, raw31220 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31220step0 = (fun i j => raw31220 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31220step0 raw31220; decide +kernel
      have hl : raw31220step0Labels = raw31220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31220 raw31220Labels permutation434 hz
    mixedMoment B raw31220step0 raw31220step0Labels = mixedMoment B raw31220step1 raw31220step1Labels := by
      have ha : raw31220step1 = (fun i j => raw31220step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31220step1 raw31220step0; decide +kernel
      have hl : raw31220step1Labels = raw31220step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31220step0 raw31220step0Labels permutation36 permutation3
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw31221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31221Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31221step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31221step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31221 raw31221Labels = mixedMoment B node739 node739Labels := by
  calc
    mixedMoment B raw31221 raw31221Labels = mixedMoment B raw31221step0 raw31221step0Labels := by
      have hz : ∀ j, raw31221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31221step0 = (fun i j => raw31221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31221step0 raw31221; decide +kernel
      have hl : raw31221step0Labels = raw31221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31221 raw31221Labels permutation346 hz
    mixedMoment B raw31221step0 raw31221step0Labels = mixedMoment B raw31221step1 raw31221step1Labels := by
      have ha : raw31221step1 = (fun i j => raw31221step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31221step1 raw31221step0; decide +kernel
      have hl : raw31221step1Labels = raw31221step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31221step0 raw31221step0Labels permutation32 permutation3
    _ = mixedMoment B node739 node739Labels := by rfl

def raw31222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31222Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31222step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31222 raw31222Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw31222 raw31222Labels = mixedMoment B raw31222step0 raw31222step0Labels := by
      have hz : ∀ j, raw31222 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31222step0 = (fun i j => raw31222 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31222step0 raw31222; decide +kernel
      have hl : raw31222step0Labels = raw31222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31222 raw31222Labels permutation346 hz
    mixedMoment B raw31222step0 raw31222step0Labels = mixedMoment B raw31222step1 raw31222step1Labels := by
      have ha : raw31222step1 = (fun i j => raw31222step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31222step1 raw31222step0; decide +kernel
      have hl : raw31222step1Labels = raw31222step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31222step0 raw31222step0Labels permutation32 permutation3
    _ = mixedMoment B node1815 node1815Labels := by rfl

def raw31223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31223Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31223 raw31223Labels = mixedMoment B node1879 node1879Labels := by
  calc
    mixedMoment B raw31223 raw31223Labels = mixedMoment B raw31223step0 raw31223step0Labels := by
      have ha : raw31223step0 = (fun i j => raw31223 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31223step0 raw31223; decide +kernel
      have hl : raw31223step0Labels = raw31223Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31223 raw31223Labels permutation176 permutation3
    _ = mixedMoment B node1879 node1879Labels := by rfl

def raw31224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31224Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31224step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31224step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31224 raw31224Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw31224 raw31224Labels = mixedMoment B raw31224step0 raw31224step0Labels := by
      have hz : ∀ j, raw31224 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31224step0 = (fun i j => raw31224 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31224step0 raw31224; decide +kernel
      have hl : raw31224step0Labels = raw31224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31224 raw31224Labels permutation346 hz
    mixedMoment B raw31224step0 raw31224step0Labels = mixedMoment B raw31224step1 raw31224step1Labels := by
      have ha : raw31224step1 = (fun i j => raw31224step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31224step1 raw31224step0; decide +kernel
      have hl : raw31224step1Labels = raw31224step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31224step0 raw31224step0Labels permutation36 permutation3
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw31225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31225Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31225step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![3, -2, -1], ![2, -1, -1]]
def raw31225step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31225step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31225 raw31225Labels = mixedMoment B node742 node742Labels := by
  calc
    mixedMoment B raw31225 raw31225Labels = mixedMoment B raw31225step0 raw31225step0Labels := by
      have hz : ∀ j, raw31225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31225step0 = (fun i j => raw31225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31225step0 raw31225; decide +kernel
      have hl : raw31225step0Labels = raw31225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31225 raw31225Labels permutation434 hz
    mixedMoment B raw31225step0 raw31225step0Labels = mixedMoment B raw31225step1 raw31225step1Labels := by
      have hz : ∀ j, raw31225step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31225step1 = (fun i j => raw31225step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31225step1 raw31225step0; decide +kernel
      have hl : raw31225step1Labels = raw31225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31225step0 raw31225step0Labels permutation80 hz
    mixedMoment B raw31225step1 raw31225step1Labels = mixedMoment B raw31225step2 raw31225step2Labels := by
      have ha : raw31225step2 = (fun i j => raw31225step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31225step2 raw31225step1; decide +kernel
      have hl : raw31225step2Labels = raw31225step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31225step1 raw31225step1Labels permutation9 permutation3
    _ = mixedMoment B node742 node742Labels := by rfl

def raw31226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31226Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31226step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![3, -2, -1], ![2, -1, -1]]
def raw31226step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31226 raw31226Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw31226 raw31226Labels = mixedMoment B raw31226step0 raw31226step0Labels := by
      have hz : ∀ j, raw31226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31226step0 = (fun i j => raw31226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31226step0 raw31226; decide +kernel
      have hl : raw31226step0Labels = raw31226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31226 raw31226Labels permutation434 hz
    mixedMoment B raw31226step0 raw31226step0Labels = mixedMoment B raw31226step1 raw31226step1Labels := by
      have hz : ∀ j, raw31226step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31226step1 = (fun i j => raw31226step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31226step1 raw31226step0; decide +kernel
      have hl : raw31226step1Labels = raw31226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31226step0 raw31226step0Labels permutation80 hz
    mixedMoment B raw31226step1 raw31226step1Labels = mixedMoment B raw31226step2 raw31226step2Labels := by
      have ha : raw31226step2 = (fun i j => raw31226step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31226step2 raw31226step1; decide +kernel
      have hl : raw31226step2Labels = raw31226step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31226step1 raw31226step1Labels permutation9 permutation3
    _ = mixedMoment B node1818 node1818Labels := by rfl

def raw31227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31227Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31227step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31227 raw31227Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw31227 raw31227Labels = mixedMoment B raw31227step0 raw31227step0Labels := by
      have hz : ∀ j, raw31227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31227step0 = (fun i j => raw31227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31227step0 raw31227; decide +kernel
      have hl : raw31227step0Labels = raw31227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31227 raw31227Labels permutation434 hz
    mixedMoment B raw31227step0 raw31227step0Labels = mixedMoment B raw31227step1 raw31227step1Labels := by
      have ha : raw31227step1 = (fun i j => raw31227step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31227step1 raw31227step0; decide +kernel
      have hl : raw31227step1Labels = raw31227step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31227step0 raw31227step0Labels permutation39 permutation3
    _ = mixedMoment B node1880 node1880Labels := by rfl

def raw31228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31228Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31228step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31228 raw31228Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw31228 raw31228Labels = mixedMoment B raw31228step0 raw31228step0Labels := by
      have hz : ∀ j, raw31228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31228step0 = (fun i j => raw31228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31228step0 raw31228; decide +kernel
      have hl : raw31228step0Labels = raw31228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31228 raw31228Labels permutation346 hz
    mixedMoment B raw31228step0 raw31228step0Labels = mixedMoment B raw31228step1 raw31228step1Labels := by
      have ha : raw31228step1 = (fun i j => raw31228step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31228step1 raw31228step0; decide +kernel
      have hl : raw31228step1Labels = raw31228step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31228step0 raw31228step0Labels permutation39 permutation3
    _ = mixedMoment B node1880 node1880Labels := by rfl

def raw31229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31229Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31229step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![3, -2, -1], ![1, 0, -1]]
def raw31229step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31229step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31229 raw31229Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw31229 raw31229Labels = mixedMoment B raw31229step0 raw31229step0Labels := by
      have hz : ∀ j, raw31229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31229step0 = (fun i j => raw31229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31229step0 raw31229; decide +kernel
      have hl : raw31229step0Labels = raw31229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31229 raw31229Labels permutation434 hz
    mixedMoment B raw31229step0 raw31229step0Labels = mixedMoment B raw31229step1 raw31229step1Labels := by
      have hz : ∀ j, raw31229step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31229step1 = (fun i j => raw31229step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31229step1 raw31229step0; decide +kernel
      have hl : raw31229step1Labels = raw31229step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31229step0 raw31229step0Labels permutation80 hz
    mixedMoment B raw31229step1 raw31229step1Labels = mixedMoment B raw31229step2 raw31229step2Labels := by
      have ha : raw31229step2 = (fun i j => raw31229step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31229step2 raw31229step1; decide +kernel
      have hl : raw31229step2Labels = raw31229step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31229step1 raw31229step1Labels permutation9 permutation3
    _ = mixedMoment B node2109 node2109Labels := by rfl

def raw31230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31230Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31230step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -1, -1], ![3, -2, -1]]
def raw31230step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31230step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31230step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31230 raw31230Labels = mixedMoment B node742 node742Labels := by
  calc
    mixedMoment B raw31230 raw31230Labels = mixedMoment B raw31230step0 raw31230step0Labels := by
      have hz : ∀ j, raw31230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31230step0 = (fun i j => raw31230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31230step0 raw31230; decide +kernel
      have hl : raw31230step0Labels = raw31230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31230 raw31230Labels permutation434 hz
    mixedMoment B raw31230step0 raw31230step0Labels = mixedMoment B raw31230step1 raw31230step1Labels := by
      have hz : ∀ j, raw31230step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31230step1 = (fun i j => raw31230step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31230step1 raw31230step0; decide +kernel
      have hl : raw31230step1Labels = raw31230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31230step0 raw31230step0Labels permutation80 hz
    mixedMoment B raw31230step1 raw31230step1Labels = mixedMoment B raw31230step2 raw31230step2Labels := by
      have ha : raw31230step2 = (fun i j => raw31230step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31230step2 raw31230step1; decide +kernel
      have hl : raw31230step2Labels = raw31230step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31230step1 raw31230step1Labels permutation8 permutation3
    _ = mixedMoment B node742 node742Labels := by rfl

def raw31231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31231Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31231step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![3, -2, -1]]
def raw31231step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31231step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31231step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31231 raw31231Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw31231 raw31231Labels = mixedMoment B raw31231step0 raw31231step0Labels := by
      have hz : ∀ j, raw31231 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31231step0 = (fun i j => raw31231 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31231step0 raw31231; decide +kernel
      have hl : raw31231step0Labels = raw31231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31231 raw31231Labels permutation434 hz
    mixedMoment B raw31231step0 raw31231step0Labels = mixedMoment B raw31231step1 raw31231step1Labels := by
      have hz : ∀ j, raw31231step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31231step1 = (fun i j => raw31231step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31231step1 raw31231step0; decide +kernel
      have hl : raw31231step1Labels = raw31231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31231step0 raw31231step0Labels permutation80 hz
    mixedMoment B raw31231step1 raw31231step1Labels = mixedMoment B raw31231step2 raw31231step2Labels := by
      have ha : raw31231step2 = (fun i j => raw31231step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31231step2 raw31231step1; decide +kernel
      have hl : raw31231step2Labels = raw31231step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31231step1 raw31231step1Labels permutation8 permutation3
    _ = mixedMoment B node1818 node1818Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
