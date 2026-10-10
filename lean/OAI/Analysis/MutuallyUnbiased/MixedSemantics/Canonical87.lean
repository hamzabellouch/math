import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11136Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11136step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw11136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11136 raw11136Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw11136 raw11136Labels = mixedMoment B raw11136step0 raw11136step0Labels := by
      have hz : ∀ j, raw11136 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11136step0 = (fun i j => raw11136 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11136step0 raw11136; decide +kernel
      have hl : raw11136step0Labels = raw11136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11136 raw11136Labels permutation434 hz
    mixedMoment B raw11136step0 raw11136step0Labels = mixedMoment B raw11136step1 raw11136step1Labels := by
      have ha : raw11136step1 = (fun i j => raw11136step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11136step1 raw11136step0; decide +kernel
      have hl : raw11136step1Labels = raw11136step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11136step0 raw11136step0Labels permutation33 permutation3
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw11137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11137Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11137step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11137 raw11137Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw11137 raw11137Labels = mixedMoment B raw11137step0 raw11137step0Labels := by
      have hz : ∀ j, raw11137 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11137step0 = (fun i j => raw11137 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11137step0 raw11137; decide +kernel
      have hl : raw11137step0Labels = raw11137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11137 raw11137Labels permutation434 hz
    mixedMoment B raw11137step0 raw11137step0Labels = mixedMoment B raw11137step1 raw11137step1Labels := by
      have ha : raw11137step1 = (fun i j => raw11137step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11137step1 raw11137step0; decide +kernel
      have hl : raw11137step1Labels = raw11137step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11137step0 raw11137step0Labels permutation40 permutation3
    _ = mixedMoment B node811 node811Labels := by rfl

def raw11138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11138Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11138step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11138 raw11138Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw11138 raw11138Labels = mixedMoment B raw11138step0 raw11138step0Labels := by
      have hz : ∀ j, raw11138 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11138step0 = (fun i j => raw11138 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11138step0 raw11138; decide +kernel
      have hl : raw11138step0Labels = raw11138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11138 raw11138Labels permutation434 hz
    mixedMoment B raw11138step0 raw11138step0Labels = mixedMoment B raw11138step1 raw11138step1Labels := by
      have ha : raw11138step1 = (fun i j => raw11138step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11138step1 raw11138step0; decide +kernel
      have hl : raw11138step1Labels = raw11138step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11138step0 raw11138step0Labels permutation40 permutation3
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw11139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11139Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11139step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11139 raw11139Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw11139 raw11139Labels = mixedMoment B raw11139step0 raw11139step0Labels := by
      have ha : raw11139step0 = (fun i j => raw11139 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11139step0 raw11139; decide +kernel
      have hl : raw11139step0Labels = raw11139Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11139 raw11139Labels permutation208 permutation3
    _ = mixedMoment B node1913 node1913Labels := by rfl

def raw11140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11140Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw11140step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw11140step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11140step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11140step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11140 raw11140Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw11140 raw11140Labels = mixedMoment B raw11140step0 raw11140step0Labels := by
      have hz : ∀ j, raw11140 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11140step0 = (fun i j => raw11140 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11140step0 raw11140; decide +kernel
      have hl : raw11140step0Labels = raw11140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11140 raw11140Labels permutation520 hz
    mixedMoment B raw11140step0 raw11140step0Labels = mixedMoment B raw11140step1 raw11140step1Labels := by
      have hz : ∀ j, raw11140step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11140step1 = (fun i j => raw11140step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11140step1 raw11140step0; decide +kernel
      have hl : raw11140step1Labels = raw11140step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11140step0 raw11140step0Labels permutation104 hz
    mixedMoment B raw11140step1 raw11140step1Labels = mixedMoment B raw11140step2 raw11140step2Labels := by
      have ha : raw11140step2 = (fun i j => raw11140step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11140step2 raw11140step1; decide +kernel
      have hl : raw11140step2Labels = raw11140step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11140step1 raw11140step1Labels permutation10 permutation3
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw11141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11141Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11141step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11141 raw11141Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw11141 raw11141Labels = mixedMoment B raw11141step0 raw11141step0Labels := by
      have hz : ∀ j, raw11141 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11141step0 = (fun i j => raw11141 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11141step0 raw11141; decide +kernel
      have hl : raw11141step0Labels = raw11141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11141 raw11141Labels permutation434 hz
    mixedMoment B raw11141step0 raw11141step0Labels = mixedMoment B raw11141step1 raw11141step1Labels := by
      have ha : raw11141step1 = (fun i j => raw11141step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11141step1 raw11141step0; decide +kernel
      have hl : raw11141step1Labels = raw11141step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11141step0 raw11141step0Labels permutation43 permutation3
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw11142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11142Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11142step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11142step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11142 raw11142Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw11142 raw11142Labels = mixedMoment B raw11142step0 raw11142step0Labels := by
      have hz : ∀ j, raw11142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11142step0 = (fun i j => raw11142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11142step0 raw11142; decide +kernel
      have hl : raw11142step0Labels = raw11142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11142 raw11142Labels permutation434 hz
    mixedMoment B raw11142step0 raw11142step0Labels = mixedMoment B raw11142step1 raw11142step1Labels := by
      have ha : raw11142step1 = (fun i j => raw11142step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11142step1 raw11142step0; decide +kernel
      have hl : raw11142step1Labels = raw11142step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11142step0 raw11142step0Labels permutation34 permutation3
    _ = mixedMoment B node811 node811Labels := by rfl

def raw11143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11143Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11143step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11143step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11143 raw11143Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw11143 raw11143Labels = mixedMoment B raw11143step0 raw11143step0Labels := by
      have hz : ∀ j, raw11143 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11143step0 = (fun i j => raw11143 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11143step0 raw11143; decide +kernel
      have hl : raw11143step0Labels = raw11143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11143 raw11143Labels permutation434 hz
    mixedMoment B raw11143step0 raw11143step0Labels = mixedMoment B raw11143step1 raw11143step1Labels := by
      have ha : raw11143step1 = (fun i j => raw11143step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11143step1 raw11143step0; decide +kernel
      have hl : raw11143step1Labels = raw11143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11143step0 raw11143step0Labels permutation34 permutation3
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw11144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11144Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11144step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11144 raw11144Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw11144 raw11144Labels = mixedMoment B raw11144step0 raw11144step0Labels := by
      have ha : raw11144step0 = (fun i j => raw11144 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11144step0 raw11144; decide +kernel
      have hl : raw11144step0Labels = raw11144Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11144 raw11144Labels permutation202 permutation3
    _ = mixedMoment B node1913 node1913Labels := by rfl

def raw11145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11145Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw11145step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw11145step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11145step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11145step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11145 raw11145Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw11145 raw11145Labels = mixedMoment B raw11145step0 raw11145step0Labels := by
      have hz : ∀ j, raw11145 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11145step0 = (fun i j => raw11145 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11145step0 raw11145; decide +kernel
      have hl : raw11145step0Labels = raw11145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11145 raw11145Labels permutation520 hz
    mixedMoment B raw11145step0 raw11145step0Labels = mixedMoment B raw11145step1 raw11145step1Labels := by
      have hz : ∀ j, raw11145step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11145step1 = (fun i j => raw11145step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11145step1 raw11145step0; decide +kernel
      have hl : raw11145step1Labels = raw11145step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11145step0 raw11145step0Labels permutation104 hz
    mixedMoment B raw11145step1 raw11145step1Labels = mixedMoment B raw11145step2 raw11145step2Labels := by
      have ha : raw11145step2 = (fun i j => raw11145step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11145step2 raw11145step1; decide +kernel
      have hl : raw11145step2Labels = raw11145step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11145step1 raw11145step1Labels permutation8 permutation3
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw11146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11146Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11146step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11146step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11146 raw11146Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw11146 raw11146Labels = mixedMoment B raw11146step0 raw11146step0Labels := by
      have hz : ∀ j, raw11146 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11146step0 = (fun i j => raw11146 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11146step0 raw11146; decide +kernel
      have hl : raw11146step0Labels = raw11146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11146 raw11146Labels permutation434 hz
    mixedMoment B raw11146step0 raw11146step0Labels = mixedMoment B raw11146step1 raw11146step1Labels := by
      have ha : raw11146step1 = (fun i j => raw11146step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11146step1 raw11146step0; decide +kernel
      have hl : raw11146step1Labels = raw11146step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11146step0 raw11146step0Labels permutation37 permutation3
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw11147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11147Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11147step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11147 raw11147Labels = mixedMoment B node786 node786Labels := by
  calc
    mixedMoment B raw11147 raw11147Labels = mixedMoment B raw11147step0 raw11147step0Labels := by
      have ha : raw11147step0 = (fun i j => raw11147 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11147step0 raw11147; decide +kernel
      have hl : raw11147step0Labels = raw11147Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11147 raw11147Labels permutation152 permutation3
    _ = mixedMoment B node786 node786Labels := by rfl

def raw11148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11148Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11148step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11148 raw11148Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw11148 raw11148Labels = mixedMoment B raw11148step0 raw11148step0Labels := by
      have ha : raw11148step0 = (fun i j => raw11148 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11148step0 raw11148; decide +kernel
      have hl : raw11148step0Labels = raw11148Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11148 raw11148Labels permutation152 permutation3
    _ = mixedMoment B node2023 node2023Labels := by rfl

def raw11149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11149 raw11149Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw11149 raw11149Labels = mixedMoment B raw11149step0 raw11149step0Labels := by
      have ha : raw11149step0 = (fun i j => raw11149 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11149step0 raw11149; decide +kernel
      have hl : raw11149step0Labels = raw11149Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11149 raw11149Labels permutation176 permutation3
    _ = mixedMoment B node2023 node2023Labels := by rfl

def raw11150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw11150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw11150step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11150step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11150 raw11150Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw11150 raw11150Labels = mixedMoment B raw11150step0 raw11150step0Labels := by
      have hz : ∀ j, raw11150 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11150step0 = (fun i j => raw11150 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11150step0 raw11150; decide +kernel
      have hl : raw11150step0Labels = raw11150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11150 raw11150Labels permutation520 hz
    mixedMoment B raw11150step0 raw11150step0Labels = mixedMoment B raw11150step1 raw11150step1Labels := by
      have ha : raw11150step1 = (fun i j => raw11150step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11150step1 raw11150step0; decide +kernel
      have hl : raw11150step1Labels = raw11150step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11150step0 raw11150step0Labels permutation32 permutation3
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw11151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11151step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11151 raw11151Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw11151 raw11151Labels = mixedMoment B raw11151step0 raw11151step0Labels := by
      have ha : raw11151step0 = (fun i j => raw11151 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11151step0 raw11151; decide +kernel
      have hl : raw11151step0Labels = raw11151Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11151 raw11151Labels permutation156 permutation3
    _ = mixedMoment B node2241 node2241Labels := by rfl

def raw11152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11152step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11152 raw11152Labels = mixedMoment B node789 node789Labels := by
  calc
    mixedMoment B raw11152 raw11152Labels = mixedMoment B raw11152step0 raw11152step0Labels := by
      have hz : ∀ j, raw11152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11152step0 = (fun i j => raw11152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11152step0 raw11152; decide +kernel
      have hl : raw11152step0Labels = raw11152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11152 raw11152Labels permutation434 hz
    mixedMoment B raw11152step0 raw11152step0Labels = mixedMoment B raw11152step1 raw11152step1Labels := by
      have ha : raw11152step1 = (fun i j => raw11152step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11152step1 raw11152step0; decide +kernel
      have hl : raw11152step1Labels = raw11152step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11152step0 raw11152step0Labels permutation33 permutation3
    _ = mixedMoment B node789 node789Labels := by rfl

def raw11153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11153step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11153 raw11153Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw11153 raw11153Labels = mixedMoment B raw11153step0 raw11153step0Labels := by
      have hz : ∀ j, raw11153 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11153step0 = (fun i j => raw11153 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11153step0 raw11153; decide +kernel
      have hl : raw11153step0Labels = raw11153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11153 raw11153Labels permutation434 hz
    mixedMoment B raw11153step0 raw11153step0Labels = mixedMoment B raw11153step1 raw11153step1Labels := by
      have ha : raw11153step1 = (fun i j => raw11153step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11153step1 raw11153step0; decide +kernel
      have hl : raw11153step1Labels = raw11153step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11153step0 raw11153step0Labels permutation33 permutation3
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw11154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw11154step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11154 raw11154Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw11154 raw11154Labels = mixedMoment B raw11154step0 raw11154step0Labels := by
      have hz : ∀ j, raw11154 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11154step0 = (fun i j => raw11154 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11154step0 raw11154; decide +kernel
      have hl : raw11154step0Labels = raw11154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11154 raw11154Labels permutation434 hz
    mixedMoment B raw11154step0 raw11154step0Labels = mixedMoment B raw11154step1 raw11154step1Labels := by
      have ha : raw11154step1 = (fun i j => raw11154step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11154step1 raw11154step0; decide +kernel
      have hl : raw11154step1Labels = raw11154step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11154step0 raw11154step0Labels permutation39 permutation3
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw11155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw11155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11155 raw11155Labels = mixedMoment B node1900 node1900Labels := by
  calc
    mixedMoment B raw11155 raw11155Labels = mixedMoment B raw11155step0 raw11155step0Labels := by
      have ha : raw11155step0 = (fun i j => raw11155 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11155step0 raw11155; decide +kernel
      have hl : raw11155step0Labels = raw11155Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11155 raw11155Labels permutation201 permutation3
    _ = mixedMoment B node1900 node1900Labels := by rfl

def raw11156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw11156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11156 raw11156Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw11156 raw11156Labels = mixedMoment B raw11156step0 raw11156step0Labels := by
      have hz : ∀ j, raw11156 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11156step0 = (fun i j => raw11156 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11156step0 raw11156; decide +kernel
      have hl : raw11156step0Labels = raw11156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11156 raw11156Labels permutation434 hz
    mixedMoment B raw11156step0 raw11156step0Labels = mixedMoment B raw11156step1 raw11156step1Labels := by
      have ha : raw11156step1 = (fun i j => raw11156step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11156step1 raw11156step0; decide +kernel
      have hl : raw11156step1Labels = raw11156step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11156step0 raw11156step0Labels permutation33 permutation3
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw11157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw11157step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11157 raw11157Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw11157 raw11157Labels = mixedMoment B raw11157step0 raw11157step0Labels := by
      have hz : ∀ j, raw11157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11157step0 = (fun i j => raw11157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11157step0 raw11157; decide +kernel
      have hl : raw11157step0Labels = raw11157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11157 raw11157Labels permutation434 hz
    mixedMoment B raw11157step0 raw11157step0Labels = mixedMoment B raw11157step1 raw11157step1Labels := by
      have ha : raw11157step1 = (fun i j => raw11157step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11157step1 raw11157step0; decide +kernel
      have hl : raw11157step1Labels = raw11157step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11157step0 raw11157step0Labels permutation32 permutation3
    _ = mixedMoment B node787 node787Labels := by rfl

def raw11158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw11158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11158 raw11158Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw11158 raw11158Labels = mixedMoment B raw11158step0 raw11158step0Labels := by
      have hz : ∀ j, raw11158 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11158step0 = (fun i j => raw11158 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11158step0 raw11158; decide +kernel
      have hl : raw11158step0Labels = raw11158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11158 raw11158Labels permutation434 hz
    mixedMoment B raw11158step0 raw11158step0Labels = mixedMoment B raw11158step1 raw11158step1Labels := by
      have ha : raw11158step1 = (fun i j => raw11158step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11158step1 raw11158step0; decide +kernel
      have hl : raw11158step1Labels = raw11158step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11158step0 raw11158step0Labels permutation32 permutation3
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw11159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw11159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11159 raw11159Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw11159 raw11159Labels = mixedMoment B raw11159step0 raw11159step0Labels := by
      have hz : ∀ j, raw11159 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11159step0 = (fun i j => raw11159 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11159step0 raw11159; decide +kernel
      have hl : raw11159step0Labels = raw11159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11159 raw11159Labels permutation434 hz
    mixedMoment B raw11159step0 raw11159step0Labels = mixedMoment B raw11159step1 raw11159step1Labels := by
      have ha : raw11159step1 = (fun i j => raw11159step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11159step1 raw11159step0; decide +kernel
      have hl : raw11159step1Labels = raw11159step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11159step0 raw11159step0Labels permutation38 permutation3
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw11160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw11160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11160step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11160 raw11160Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw11160 raw11160Labels = mixedMoment B raw11160step0 raw11160step0Labels := by
      have ha : raw11160step0 = (fun i j => raw11160 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11160step0 raw11160; decide +kernel
      have hl : raw11160step0Labels = raw11160Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11160 raw11160Labels permutation200 permutation3
    _ = mixedMoment B node1898 node1898Labels := by rfl

def raw11161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw11161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw11161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw11161step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11161step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11161 raw11161Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw11161 raw11161Labels = mixedMoment B raw11161step0 raw11161step0Labels := by
      have hz : ∀ j, raw11161 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11161step0 = (fun i j => raw11161 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11161step0 raw11161; decide +kernel
      have hl : raw11161step0Labels = raw11161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11161 raw11161Labels permutation520 hz
    mixedMoment B raw11161step0 raw11161step0Labels = mixedMoment B raw11161step1 raw11161step1Labels := by
      have hz : ∀ j, raw11161step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11161step1 = (fun i j => raw11161step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11161step1 raw11161step0; decide +kernel
      have hl : raw11161step1Labels = raw11161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11161step0 raw11161step0Labels permutation104 hz
    mixedMoment B raw11161step1 raw11161step1Labels = mixedMoment B raw11161step2 raw11161step2Labels := by
      have ha : raw11161step2 = (fun i j => raw11161step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11161step2 raw11161step1; decide +kernel
      have hl : raw11161step2Labels = raw11161step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11161step1 raw11161step1Labels permutation8 permutation3
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw11162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11162step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11162step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11162step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11162step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11162 raw11162Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw11162 raw11162Labels = mixedMoment B raw11162step0 raw11162step0Labels := by
      have hz : ∀ j, raw11162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11162step0 = (fun i j => raw11162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11162step0 raw11162; decide +kernel
      have hl : raw11162step0Labels = raw11162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11162 raw11162Labels permutation434 hz
    mixedMoment B raw11162step0 raw11162step0Labels = mixedMoment B raw11162step1 raw11162step1Labels := by
      have ha : raw11162step1 = (fun i j => raw11162step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11162step1 raw11162step0; decide +kernel
      have hl : raw11162step1Labels = raw11162step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11162step0 raw11162step0Labels permutation53 permutation4
    mixedMoment B raw11162step1 raw11162step1Labels = mixedMoment B raw11162step2 raw11162step2Labels := by
      have ha : raw11162step2 = -raw11162step1 := by apply Matrix.ext; change ∀ i j, raw11162step2 i j = -(raw11162step1 i j); unfold raw11162step2 raw11162step1; decide +kernel
      have hl : raw11162step2Labels = raw11162step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11162step2 raw11162step2Labels = mixedMoment B raw11162step3 raw11162step3Labels := by
      have ha : raw11162step3 = raw11162step2 := by apply Matrix.ext; unfold raw11162step3 raw11162step2; decide +kernel
      have hl : raw11162step2Labels = labelEmbedding7 ∘ raw11162step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11162step2 raw11162step2Labels raw11162step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw11163 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11163step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11163step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11163step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11163step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11163 raw11163Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw11163 raw11163Labels = mixedMoment B raw11163step0 raw11163step0Labels := by
      have ha : raw11163step0 = (fun i j => raw11163 (permutation221 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11163step0 raw11163; decide +kernel
      have hl : raw11163step0Labels = raw11163Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11163 raw11163Labels permutation221 permutation4
    mixedMoment B raw11163step0 raw11163step0Labels = mixedMoment B raw11163step1 raw11163step1Labels := by
      have ha : raw11163step1 = -raw11163step0 := by apply Matrix.ext; change ∀ i j, raw11163step1 i j = -(raw11163step0 i j); unfold raw11163step1 raw11163step0; decide +kernel
      have hl : raw11163step1Labels = raw11163step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11163step1 raw11163step1Labels = mixedMoment B raw11163step2 raw11163step2Labels := by
      have ha : raw11163step2 = raw11163step1 := by apply Matrix.ext; unfold raw11163step2 raw11163step1; decide +kernel
      have hl : raw11163step1Labels = labelEmbedding7 ∘ raw11163step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11163step1 raw11163step1Labels raw11163step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw11164 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11164step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11164step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11164step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11164step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11164 raw11164Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw11164 raw11164Labels = mixedMoment B raw11164step0 raw11164step0Labels := by
      have hz : ∀ j, raw11164 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11164step0 = (fun i j => raw11164 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11164step0 raw11164; decide +kernel
      have hl : raw11164step0Labels = raw11164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11164 raw11164Labels permutation434 hz
    mixedMoment B raw11164step0 raw11164step0Labels = mixedMoment B raw11164step1 raw11164step1Labels := by
      have ha : raw11164step1 = (fun i j => raw11164step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11164step1 raw11164step0; decide +kernel
      have hl : raw11164step1Labels = raw11164step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11164step0 raw11164step0Labels permutation53 permutation4
    mixedMoment B raw11164step1 raw11164step1Labels = mixedMoment B raw11164step2 raw11164step2Labels := by
      have ha : raw11164step2 = -raw11164step1 := by apply Matrix.ext; change ∀ i j, raw11164step2 i j = -(raw11164step1 i j); unfold raw11164step2 raw11164step1; decide +kernel
      have hl : raw11164step2Labels = raw11164step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11164step2 raw11164step2Labels = mixedMoment B raw11164step3 raw11164step3Labels := by
      have ha : raw11164step3 = raw11164step2 := by apply Matrix.ext; unfold raw11164step3 raw11164step2; decide +kernel
      have hl : raw11164step2Labels = labelEmbedding7 ∘ raw11164step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11164step2 raw11164step2Labels raw11164step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw11165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11165step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11165step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11165step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11165step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11165 raw11165Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw11165 raw11165Labels = mixedMoment B raw11165step0 raw11165step0Labels := by
      have hz : ∀ j, raw11165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11165step0 = (fun i j => raw11165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11165step0 raw11165; decide +kernel
      have hl : raw11165step0Labels = raw11165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11165 raw11165Labels permutation434 hz
    mixedMoment B raw11165step0 raw11165step0Labels = mixedMoment B raw11165step1 raw11165step1Labels := by
      have ha : raw11165step1 = (fun i j => raw11165step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11165step1 raw11165step0; decide +kernel
      have hl : raw11165step1Labels = raw11165step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11165step0 raw11165step0Labels permutation51 permutation4
    mixedMoment B raw11165step1 raw11165step1Labels = mixedMoment B raw11165step2 raw11165step2Labels := by
      have ha : raw11165step2 = -raw11165step1 := by apply Matrix.ext; change ∀ i j, raw11165step2 i j = -(raw11165step1 i j); unfold raw11165step2 raw11165step1; decide +kernel
      have hl : raw11165step2Labels = raw11165step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11165step2 raw11165step2Labels = mixedMoment B raw11165step3 raw11165step3Labels := by
      have ha : raw11165step3 = raw11165step2 := by apply Matrix.ext; unfold raw11165step3 raw11165step2; decide +kernel
      have hl : raw11165step2Labels = labelEmbedding7 ∘ raw11165step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11165step2 raw11165step2Labels raw11165step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw11166 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11166step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11166step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw11166step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11166step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11166step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11166step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11166step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11166 raw11166Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw11166 raw11166Labels = mixedMoment B raw11166step0 raw11166step0Labels := by
      have hz : ∀ j, raw11166 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11166step0 = (fun i j => raw11166 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11166step0 raw11166; decide +kernel
      have hl : raw11166step0Labels = raw11166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11166 raw11166Labels permutation434 hz
    mixedMoment B raw11166step0 raw11166step0Labels = mixedMoment B raw11166step1 raw11166step1Labels := by
      have hz : ∀ j, raw11166step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11166step1 = (fun i j => raw11166step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11166step1 raw11166step0; decide +kernel
      have hl : raw11166step1Labels = raw11166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11166step0 raw11166step0Labels permutation56 hz
    mixedMoment B raw11166step1 raw11166step1Labels = mixedMoment B raw11166step2 raw11166step2Labels := by
      have ha : raw11166step2 = (fun i j => raw11166step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11166step2 raw11166step1; decide +kernel
      have hl : raw11166step2Labels = raw11166step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11166step1 raw11166step1Labels permutation13 permutation4
    mixedMoment B raw11166step2 raw11166step2Labels = mixedMoment B raw11166step3 raw11166step3Labels := by
      have ha : raw11166step3 = -raw11166step2 := by apply Matrix.ext; change ∀ i j, raw11166step3 i j = -(raw11166step2 i j); unfold raw11166step3 raw11166step2; decide +kernel
      have hl : raw11166step3Labels = raw11166step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11166step3 raw11166step3Labels = mixedMoment B raw11166step4 raw11166step4Labels := by
      have ha : raw11166step4 = raw11166step3 := by apply Matrix.ext; unfold raw11166step4 raw11166step3; decide +kernel
      have hl : raw11166step3Labels = labelEmbedding7 ∘ raw11166step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11166step3 raw11166step3Labels raw11166step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw11167 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11167step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11167step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11167step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11167step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11167 raw11167Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw11167 raw11167Labels = mixedMoment B raw11167step0 raw11167step0Labels := by
      have ha : raw11167step0 = (fun i j => raw11167 (permutation219 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11167step0 raw11167; decide +kernel
      have hl : raw11167step0Labels = raw11167Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11167 raw11167Labels permutation219 permutation4
    mixedMoment B raw11167step0 raw11167step0Labels = mixedMoment B raw11167step1 raw11167step1Labels := by
      have ha : raw11167step1 = -raw11167step0 := by apply Matrix.ext; change ∀ i j, raw11167step1 i j = -(raw11167step0 i j); unfold raw11167step1 raw11167step0; decide +kernel
      have hl : raw11167step1Labels = raw11167step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11167step1 raw11167step1Labels = mixedMoment B raw11167step2 raw11167step2Labels := by
      have ha : raw11167step2 = raw11167step1 := by apply Matrix.ext; unfold raw11167step2 raw11167step1; decide +kernel
      have hl : raw11167step1Labels = labelEmbedding7 ∘ raw11167step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11167step1 raw11167step1Labels raw11167step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw11168 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11168step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11168step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11168step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11168step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11168step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11168 raw11168Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw11168 raw11168Labels = mixedMoment B raw11168step0 raw11168step0Labels := by
      have hz : ∀ j, raw11168 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11168step0 = (fun i j => raw11168 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11168step0 raw11168; decide +kernel
      have hl : raw11168step0Labels = raw11168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11168 raw11168Labels permutation434 hz
    mixedMoment B raw11168step0 raw11168step0Labels = mixedMoment B raw11168step1 raw11168step1Labels := by
      have ha : raw11168step1 = (fun i j => raw11168step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11168step1 raw11168step0; decide +kernel
      have hl : raw11168step1Labels = raw11168step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11168step0 raw11168step0Labels permutation51 permutation4
    mixedMoment B raw11168step1 raw11168step1Labels = mixedMoment B raw11168step2 raw11168step2Labels := by
      have ha : raw11168step2 = -raw11168step1 := by apply Matrix.ext; change ∀ i j, raw11168step2 i j = -(raw11168step1 i j); unfold raw11168step2 raw11168step1; decide +kernel
      have hl : raw11168step2Labels = raw11168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11168step2 raw11168step2Labels = mixedMoment B raw11168step3 raw11168step3Labels := by
      have ha : raw11168step3 = raw11168step2 := by apply Matrix.ext; unfold raw11168step3 raw11168step2; decide +kernel
      have hl : raw11168step2Labels = labelEmbedding7 ∘ raw11168step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11168step2 raw11168step2Labels raw11168step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw11169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw11169step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11169step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11169step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11169step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11169 raw11169Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw11169 raw11169Labels = mixedMoment B raw11169step0 raw11169step0Labels := by
      have hz : ∀ j, raw11169 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11169step0 = (fun i j => raw11169 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11169step0 raw11169; decide +kernel
      have hl : raw11169step0Labels = raw11169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11169 raw11169Labels permutation434 hz
    mixedMoment B raw11169step0 raw11169step0Labels = mixedMoment B raw11169step1 raw11169step1Labels := by
      have ha : raw11169step1 = (fun i j => raw11169step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11169step1 raw11169step0; decide +kernel
      have hl : raw11169step1Labels = raw11169step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11169step0 raw11169step0Labels permutation50 permutation4
    mixedMoment B raw11169step1 raw11169step1Labels = mixedMoment B raw11169step2 raw11169step2Labels := by
      have ha : raw11169step2 = -raw11169step1 := by apply Matrix.ext; change ∀ i j, raw11169step2 i j = -(raw11169step1 i j); unfold raw11169step2 raw11169step1; decide +kernel
      have hl : raw11169step2Labels = raw11169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11169step2 raw11169step2Labels = mixedMoment B raw11169step3 raw11169step3Labels := by
      have ha : raw11169step3 = raw11169step2 := by apply Matrix.ext; unfold raw11169step3 raw11169step2; decide +kernel
      have hl : raw11169step2Labels = labelEmbedding7 ∘ raw11169step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11169step2 raw11169step2Labels raw11169step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw11170 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw11170step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11170step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11170step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11170step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11170step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11170 raw11170Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw11170 raw11170Labels = mixedMoment B raw11170step0 raw11170step0Labels := by
      have ha : raw11170step0 = (fun i j => raw11170 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11170step0 raw11170; decide +kernel
      have hl : raw11170step0Labels = raw11170Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11170 raw11170Labels permutation218 permutation4
    mixedMoment B raw11170step0 raw11170step0Labels = mixedMoment B raw11170step1 raw11170step1Labels := by
      have ha : raw11170step1 = -raw11170step0 := by apply Matrix.ext; change ∀ i j, raw11170step1 i j = -(raw11170step0 i j); unfold raw11170step1 raw11170step0; decide +kernel
      have hl : raw11170step1Labels = raw11170step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11170step1 raw11170step1Labels = mixedMoment B raw11170step2 raw11170step2Labels := by
      have ha : raw11170step2 = raw11170step1 := by apply Matrix.ext; unfold raw11170step2 raw11170step1; decide +kernel
      have hl : raw11170step1Labels = labelEmbedding7 ∘ raw11170step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11170step1 raw11170step1Labels raw11170step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw11171 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw11171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw11171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw11171step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11171step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11171step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11171step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11171 raw11171Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw11171 raw11171Labels = mixedMoment B raw11171step0 raw11171step0Labels := by
      have hz : ∀ j, raw11171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11171step0 = (fun i j => raw11171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11171step0 raw11171; decide +kernel
      have hl : raw11171step0Labels = raw11171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11171 raw11171Labels permutation434 hz
    mixedMoment B raw11171step0 raw11171step0Labels = mixedMoment B raw11171step1 raw11171step1Labels := by
      have ha : raw11171step1 = (fun i j => raw11171step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11171step1 raw11171step0; decide +kernel
      have hl : raw11171step1Labels = raw11171step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11171step0 raw11171step0Labels permutation50 permutation4
    mixedMoment B raw11171step1 raw11171step1Labels = mixedMoment B raw11171step2 raw11171step2Labels := by
      have ha : raw11171step2 = -raw11171step1 := by apply Matrix.ext; change ∀ i j, raw11171step2 i j = -(raw11171step1 i j); unfold raw11171step2 raw11171step1; decide +kernel
      have hl : raw11171step2Labels = raw11171step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11171step2 raw11171step2Labels = mixedMoment B raw11171step3 raw11171step3Labels := by
      have ha : raw11171step3 = raw11171step2 := by apply Matrix.ext; unfold raw11171step3 raw11171step2; decide +kernel
      have hl : raw11171step2Labels = labelEmbedding7 ∘ raw11171step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11171step2 raw11171step2Labels raw11171step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw11172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11172step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11172step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11172step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11172step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11172step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11172 raw11172Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw11172 raw11172Labels = mixedMoment B raw11172step0 raw11172step0Labels := by
      have hz : ∀ j, raw11172 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11172step0 = (fun i j => raw11172 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11172step0 raw11172; decide +kernel
      have hl : raw11172step0Labels = raw11172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11172 raw11172Labels permutation434 hz
    mixedMoment B raw11172step0 raw11172step0Labels = mixedMoment B raw11172step1 raw11172step1Labels := by
      have ha : raw11172step1 = (fun i j => raw11172step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11172step1 raw11172step0; decide +kernel
      have hl : raw11172step1Labels = raw11172step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11172step0 raw11172step0Labels permutation32 permutation4
    mixedMoment B raw11172step1 raw11172step1Labels = mixedMoment B raw11172step2 raw11172step2Labels := by
      have ha : raw11172step2 = -raw11172step1 := by apply Matrix.ext; change ∀ i j, raw11172step2 i j = -(raw11172step1 i j); unfold raw11172step2 raw11172step1; decide +kernel
      have hl : raw11172step2Labels = raw11172step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11172step2 raw11172step2Labels = mixedMoment B raw11172step3 raw11172step3Labels := by
      have ha : raw11172step3 = raw11172step2 := by apply Matrix.ext; unfold raw11172step3 raw11172step2; decide +kernel
      have hl : raw11172step2Labels = labelEmbedding7 ∘ raw11172step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11172step2 raw11172step2Labels raw11172step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw11173 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11173step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11173step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11173step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11173 raw11173Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw11173 raw11173Labels = mixedMoment B raw11173step0 raw11173step0Labels := by
      have hz : ∀ j, raw11173 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11173step0 = (fun i j => raw11173 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11173step0 raw11173; decide +kernel
      have hl : raw11173step0Labels = raw11173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11173 raw11173Labels permutation434 hz
    mixedMoment B raw11173step0 raw11173step0Labels = mixedMoment B raw11173step1 raw11173step1Labels := by
      have hz : ∀ j, raw11173step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11173step1 = (fun i j => raw11173step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11173step1 raw11173step0; decide +kernel
      have hl : raw11173step1Labels = raw11173step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11173step0 raw11173step0Labels permutation56 hz
    mixedMoment B raw11173step1 raw11173step1Labels = mixedMoment B raw11173step2 raw11173step2Labels := by
      have ha : raw11173step2 = (fun i j => raw11173step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11173step2 raw11173step1; decide +kernel
      have hl : raw11173step2Labels = raw11173step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11173step1 raw11173step1Labels permutation8 permutation6
    mixedMoment B raw11173step2 raw11173step2Labels = mixedMoment B raw11173step3 raw11173step3Labels := by
      have ha : raw11173step3 = raw11173step2 := by apply Matrix.ext; unfold raw11173step3 raw11173step2; decide +kernel
      have hl : raw11173step2Labels = labelEmbedding9 ∘ raw11173step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11173step2 raw11173step2Labels raw11173step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw11174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11174 raw11174Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw11174 raw11174Labels = mixedMoment B raw11174step0 raw11174step0Labels := by
      have hz : ∀ j, raw11174 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11174step0 = (fun i j => raw11174 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11174step0 raw11174; decide +kernel
      have hl : raw11174step0Labels = raw11174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11174 raw11174Labels permutation434 hz
    mixedMoment B raw11174step0 raw11174step0Labels = mixedMoment B raw11174step1 raw11174step1Labels := by
      have ha : raw11174step1 = (fun i j => raw11174step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11174step1 raw11174step0; decide +kernel
      have hl : raw11174step1Labels = raw11174step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11174step0 raw11174step0Labels permutation38 permutation6
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw11175 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11175 raw11175Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw11175 raw11175Labels = mixedMoment B raw11175step0 raw11175step0Labels := by
      have ha : raw11175step0 = (fun i j => raw11175 (permutation206 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11175step0 raw11175; decide +kernel
      have hl : raw11175step0Labels = raw11175Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11175 raw11175Labels permutation206 permutation6
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw11176 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw11176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11176 raw11176Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw11176 raw11176Labels = mixedMoment B raw11176step0 raw11176step0Labels := by
      have hz : ∀ j, raw11176 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11176step0 = (fun i j => raw11176 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11176step0 raw11176; decide +kernel
      have hl : raw11176step0Labels = raw11176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11176 raw11176Labels permutation434 hz
    mixedMoment B raw11176step0 raw11176step0Labels = mixedMoment B raw11176step1 raw11176step1Labels := by
      have ha : raw11176step1 = (fun i j => raw11176step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11176step1 raw11176step0; decide +kernel
      have hl : raw11176step1Labels = raw11176step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11176step0 raw11176step0Labels permutation38 permutation6
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw11177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11177 raw11177Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw11177 raw11177Labels = mixedMoment B raw11177step0 raw11177step0Labels := by
      have hz : ∀ j, raw11177 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11177step0 = (fun i j => raw11177 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11177step0 raw11177; decide +kernel
      have hl : raw11177step0Labels = raw11177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11177 raw11177Labels permutation434 hz
    mixedMoment B raw11177step0 raw11177step0Labels = mixedMoment B raw11177step1 raw11177step1Labels := by
      have ha : raw11177step1 = (fun i j => raw11177step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11177step1 raw11177step0; decide +kernel
      have hl : raw11177step1Labels = raw11177step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11177step0 raw11177step0Labels permutation32 permutation6
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw11178 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11178step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11178 raw11178Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw11178 raw11178Labels = mixedMoment B raw11178step0 raw11178step0Labels := by
      have hz : ∀ j, raw11178 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11178step0 = (fun i j => raw11178 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11178step0 raw11178; decide +kernel
      have hl : raw11178step0Labels = raw11178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11178 raw11178Labels permutation434 hz
    mixedMoment B raw11178step0 raw11178step0Labels = mixedMoment B raw11178step1 raw11178step1Labels := by
      have hz : ∀ j, raw11178step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11178step1 = (fun i j => raw11178step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11178step1 raw11178step0; decide +kernel
      have hl : raw11178step1Labels = raw11178step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11178step0 raw11178step0Labels permutation56 hz
    mixedMoment B raw11178step1 raw11178step1Labels = mixedMoment B raw11178step2 raw11178step2Labels := by
      have ha : raw11178step2 = (fun i j => raw11178step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11178step2 raw11178step1; decide +kernel
      have hl : raw11178step2Labels = raw11178step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11178step1 raw11178step1Labels permutation8 permutation6
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw11179 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw11179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11179 raw11179Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw11179 raw11179Labels = mixedMoment B raw11179step0 raw11179step0Labels := by
      have ha : raw11179step0 = (fun i j => raw11179 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11179step0 raw11179; decide +kernel
      have hl : raw11179step0Labels = raw11179Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11179 raw11179Labels permutation200 permutation6
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw11180 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw11180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11180 raw11180Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw11180 raw11180Labels = mixedMoment B raw11180step0 raw11180step0Labels := by
      have hz : ∀ j, raw11180 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11180step0 = (fun i j => raw11180 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11180step0 raw11180; decide +kernel
      have hl : raw11180step0Labels = raw11180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11180 raw11180Labels permutation434 hz
    mixedMoment B raw11180step0 raw11180step0Labels = mixedMoment B raw11180step1 raw11180step1Labels := by
      have ha : raw11180step1 = (fun i j => raw11180step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11180step1 raw11180step0; decide +kernel
      have hl : raw11180step1Labels = raw11180step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11180step0 raw11180step0Labels permutation32 permutation6
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw11181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11181 raw11181Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw11181 raw11181Labels = mixedMoment B raw11181step0 raw11181step0Labels := by
      have hz : ∀ j, raw11181 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11181step0 = (fun i j => raw11181 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11181step0 raw11181; decide +kernel
      have hl : raw11181step0Labels = raw11181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11181 raw11181Labels permutation434 hz
    mixedMoment B raw11181step0 raw11181step0Labels = mixedMoment B raw11181step1 raw11181step1Labels := by
      have ha : raw11181step1 = (fun i j => raw11181step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11181step1 raw11181step0; decide +kernel
      have hl : raw11181step1Labels = raw11181step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11181step0 raw11181step0Labels permutation32 permutation6
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw11182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11182 raw11182Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw11182 raw11182Labels = mixedMoment B raw11182step0 raw11182step0Labels := by
      have ha : raw11182step0 = (fun i j => raw11182 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11182step0 raw11182; decide +kernel
      have hl : raw11182step0Labels = raw11182Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11182 raw11182Labels permutation200 permutation6
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw11183 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw11183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw11183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11183 raw11183Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw11183 raw11183Labels = mixedMoment B raw11183step0 raw11183step0Labels := by
      have hz : ∀ j, raw11183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11183step0 = (fun i j => raw11183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11183step0 raw11183; decide +kernel
      have hl : raw11183step0Labels = raw11183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11183 raw11183Labels permutation434 hz
    mixedMoment B raw11183step0 raw11183step0Labels = mixedMoment B raw11183step1 raw11183step1Labels := by
      have ha : raw11183step1 = (fun i j => raw11183step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11183step1 raw11183step0; decide +kernel
      have hl : raw11183step1Labels = raw11183step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11183step0 raw11183step0Labels permutation32 permutation6
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw11184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11184 raw11184Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw11184 raw11184Labels = mixedMoment B raw11184step0 raw11184step0Labels := by
      have hz : ∀ j, raw11184 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11184step0 = (fun i j => raw11184 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11184step0 raw11184; decide +kernel
      have hl : raw11184step0Labels = raw11184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11184 raw11184Labels permutation434 hz
    mixedMoment B raw11184step0 raw11184step0Labels = mixedMoment B raw11184step1 raw11184step1Labels := by
      have ha : raw11184step1 = (fun i j => raw11184step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11184step1 raw11184step0; decide +kernel
      have hl : raw11184step1Labels = raw11184step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11184step0 raw11184step0Labels permutation32 permutation6
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw11185 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11185step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11185 raw11185Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw11185 raw11185Labels = mixedMoment B raw11185step0 raw11185step0Labels := by
      have hz : ∀ j, raw11185 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11185step0 = (fun i j => raw11185 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11185step0 raw11185; decide +kernel
      have hl : raw11185step0Labels = raw11185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11185 raw11185Labels permutation434 hz
    mixedMoment B raw11185step0 raw11185step0Labels = mixedMoment B raw11185step1 raw11185step1Labels := by
      have hz : ∀ j, raw11185step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11185step1 = (fun i j => raw11185step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11185step1 raw11185step0; decide +kernel
      have hl : raw11185step1Labels = raw11185step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11185step0 raw11185step0Labels permutation56 hz
    mixedMoment B raw11185step1 raw11185step1Labels = mixedMoment B raw11185step2 raw11185step2Labels := by
      have ha : raw11185step2 = (fun i j => raw11185step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11185step2 raw11185step1; decide +kernel
      have hl : raw11185step2Labels = raw11185step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11185step1 raw11185step1Labels permutation8 permutation6
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw11186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11186step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11186 raw11186Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw11186 raw11186Labels = mixedMoment B raw11186step0 raw11186step0Labels := by
      have hz : ∀ j, raw11186 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11186step0 = (fun i j => raw11186 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11186step0 raw11186; decide +kernel
      have hl : raw11186step0Labels = raw11186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11186 raw11186Labels permutation434 hz
    mixedMoment B raw11186step0 raw11186step0Labels = mixedMoment B raw11186step1 raw11186step1Labels := by
      have ha : raw11186step1 = (fun i j => raw11186step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11186step1 raw11186step0; decide +kernel
      have hl : raw11186step1Labels = raw11186step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11186step0 raw11186step0Labels permutation55 permutation5
    mixedMoment B raw11186step1 raw11186step1Labels = mixedMoment B raw11186step2 raw11186step2Labels := by
      have ha : raw11186step2 = -raw11186step1 := by apply Matrix.ext; change ∀ i j, raw11186step2 i j = -(raw11186step1 i j); unfold raw11186step2 raw11186step1; decide +kernel
      have hl : raw11186step2Labels = raw11186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11186step2 raw11186step2Labels = mixedMoment B raw11186step3 raw11186step3Labels := by
      have ha : raw11186step3 = raw11186step2 := by apply Matrix.ext; unfold raw11186step3 raw11186step2; decide +kernel
      have hl : raw11186step2Labels = labelEmbedding1 ∘ raw11186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11186step2 raw11186step2Labels raw11186step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1367 node1367Labels := by rfl

def raw11187 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11187 raw11187Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw11187 raw11187Labels = mixedMoment B raw11187step0 raw11187step0Labels := by
      have ha : raw11187step0 = (fun i j => raw11187 (permutation223 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11187step0 raw11187; decide +kernel
      have hl : raw11187step0Labels = raw11187Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11187 raw11187Labels permutation223 permutation5
    mixedMoment B raw11187step0 raw11187step0Labels = mixedMoment B raw11187step1 raw11187step1Labels := by
      have ha : raw11187step1 = -raw11187step0 := by apply Matrix.ext; change ∀ i j, raw11187step1 i j = -(raw11187step0 i j); unfold raw11187step1 raw11187step0; decide +kernel
      have hl : raw11187step1Labels = raw11187step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11187step1 raw11187step1Labels = mixedMoment B raw11187step2 raw11187step2Labels := by
      have ha : raw11187step2 = raw11187step1 := by apply Matrix.ext; unfold raw11187step2 raw11187step1; decide +kernel
      have hl : raw11187step1Labels = labelEmbedding1 ∘ raw11187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11187step1 raw11187step1Labels raw11187step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3196 node3196Labels := by rfl

def raw11188 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11188step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11188 raw11188Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw11188 raw11188Labels = mixedMoment B raw11188step0 raw11188step0Labels := by
      have hz : ∀ j, raw11188 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11188step0 = (fun i j => raw11188 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11188step0 raw11188; decide +kernel
      have hl : raw11188step0Labels = raw11188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11188 raw11188Labels permutation434 hz
    mixedMoment B raw11188step0 raw11188step0Labels = mixedMoment B raw11188step1 raw11188step1Labels := by
      have ha : raw11188step1 = (fun i j => raw11188step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11188step1 raw11188step0; decide +kernel
      have hl : raw11188step1Labels = raw11188step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11188step0 raw11188step0Labels permutation55 permutation5
    mixedMoment B raw11188step1 raw11188step1Labels = mixedMoment B raw11188step2 raw11188step2Labels := by
      have ha : raw11188step2 = -raw11188step1 := by apply Matrix.ext; change ∀ i j, raw11188step2 i j = -(raw11188step1 i j); unfold raw11188step2 raw11188step1; decide +kernel
      have hl : raw11188step2Labels = raw11188step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11188step2 raw11188step2Labels = mixedMoment B raw11188step3 raw11188step3Labels := by
      have ha : raw11188step3 = raw11188step2 := by apply Matrix.ext; unfold raw11188step3 raw11188step2; decide +kernel
      have hl : raw11188step2Labels = labelEmbedding1 ∘ raw11188step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11188step2 raw11188step2Labels raw11188step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3156 node3156Labels := by rfl

def raw11189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11189 raw11189Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw11189 raw11189Labels = mixedMoment B raw11189step0 raw11189step0Labels := by
      have hz : ∀ j, raw11189 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11189step0 = (fun i j => raw11189 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11189step0 raw11189; decide +kernel
      have hl : raw11189step0Labels = raw11189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11189 raw11189Labels permutation434 hz
    mixedMoment B raw11189step0 raw11189step0Labels = mixedMoment B raw11189step1 raw11189step1Labels := by
      have ha : raw11189step1 = (fun i j => raw11189step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11189step1 raw11189step0; decide +kernel
      have hl : raw11189step1Labels = raw11189step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11189step0 raw11189step0Labels permutation54 permutation5
    mixedMoment B raw11189step1 raw11189step1Labels = mixedMoment B raw11189step2 raw11189step2Labels := by
      have ha : raw11189step2 = -raw11189step1 := by apply Matrix.ext; change ∀ i j, raw11189step2 i j = -(raw11189step1 i j); unfold raw11189step2 raw11189step1; decide +kernel
      have hl : raw11189step2Labels = raw11189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11189step2 raw11189step2Labels = mixedMoment B raw11189step3 raw11189step3Labels := by
      have ha : raw11189step3 = raw11189step2 := by apply Matrix.ext; unfold raw11189step3 raw11189step2; decide +kernel
      have hl : raw11189step2Labels = labelEmbedding1 ∘ raw11189step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11189step2 raw11189step2Labels raw11189step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1367 node1367Labels := by rfl

def raw11190 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11190step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11190step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11190step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw11190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11190step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw11190step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11190step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw11190step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11190 raw11190Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw11190 raw11190Labels = mixedMoment B raw11190step0 raw11190step0Labels := by
      have hz : ∀ j, raw11190 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11190step0 = (fun i j => raw11190 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11190step0 raw11190; decide +kernel
      have hl : raw11190step0Labels = raw11190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11190 raw11190Labels permutation434 hz
    mixedMoment B raw11190step0 raw11190step0Labels = mixedMoment B raw11190step1 raw11190step1Labels := by
      have hz : ∀ j, raw11190step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11190step1 = (fun i j => raw11190step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11190step1 raw11190step0; decide +kernel
      have hl : raw11190step1Labels = raw11190step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11190step0 raw11190step0Labels permutation56 hz
    mixedMoment B raw11190step1 raw11190step1Labels = mixedMoment B raw11190step2 raw11190step2Labels := by
      have ha : raw11190step2 = (fun i j => raw11190step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11190step2 raw11190step1; decide +kernel
      have hl : raw11190step2Labels = raw11190step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11190step1 raw11190step1Labels permutation13 permutation5
    mixedMoment B raw11190step2 raw11190step2Labels = mixedMoment B raw11190step3 raw11190step3Labels := by
      have ha : raw11190step3 = -raw11190step2 := by apply Matrix.ext; change ∀ i j, raw11190step3 i j = -(raw11190step2 i j); unfold raw11190step3 raw11190step2; decide +kernel
      have hl : raw11190step3Labels = raw11190step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11190step3 raw11190step3Labels = mixedMoment B raw11190step4 raw11190step4Labels := by
      have ha : raw11190step4 = raw11190step3 := by apply Matrix.ext; unfold raw11190step4 raw11190step3; decide +kernel
      have hl : raw11190step3Labels = labelEmbedding1 ∘ raw11190step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11190step3 raw11190step3Labels raw11190step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3224 node3224Labels := by rfl

def raw11191 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11191step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11191step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11191step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11191 raw11191Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw11191 raw11191Labels = mixedMoment B raw11191step0 raw11191step0Labels := by
      have ha : raw11191step0 = (fun i j => raw11191 (permutation222 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11191step0 raw11191; decide +kernel
      have hl : raw11191step0Labels = raw11191Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11191 raw11191Labels permutation222 permutation5
    mixedMoment B raw11191step0 raw11191step0Labels = mixedMoment B raw11191step1 raw11191step1Labels := by
      have ha : raw11191step1 = -raw11191step0 := by apply Matrix.ext; change ∀ i j, raw11191step1 i j = -(raw11191step0 i j); unfold raw11191step1 raw11191step0; decide +kernel
      have hl : raw11191step1Labels = raw11191step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11191step1 raw11191step1Labels = mixedMoment B raw11191step2 raw11191step2Labels := by
      have ha : raw11191step2 = raw11191step1 := by apply Matrix.ext; unfold raw11191step2 raw11191step1; decide +kernel
      have hl : raw11191step1Labels = labelEmbedding1 ∘ raw11191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11191step1 raw11191step1Labels raw11191step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3196 node3196Labels := by rfl

def raw11192 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw11192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11192step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11192step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw11192step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11192 raw11192Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw11192 raw11192Labels = mixedMoment B raw11192step0 raw11192step0Labels := by
      have hz : ∀ j, raw11192 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11192step0 = (fun i j => raw11192 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11192step0 raw11192; decide +kernel
      have hl : raw11192step0Labels = raw11192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11192 raw11192Labels permutation434 hz
    mixedMoment B raw11192step0 raw11192step0Labels = mixedMoment B raw11192step1 raw11192step1Labels := by
      have ha : raw11192step1 = (fun i j => raw11192step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11192step1 raw11192step0; decide +kernel
      have hl : raw11192step1Labels = raw11192step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11192step0 raw11192step0Labels permutation54 permutation5
    mixedMoment B raw11192step1 raw11192step1Labels = mixedMoment B raw11192step2 raw11192step2Labels := by
      have ha : raw11192step2 = -raw11192step1 := by apply Matrix.ext; change ∀ i j, raw11192step2 i j = -(raw11192step1 i j); unfold raw11192step2 raw11192step1; decide +kernel
      have hl : raw11192step2Labels = raw11192step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11192step2 raw11192step2Labels = mixedMoment B raw11192step3 raw11192step3Labels := by
      have ha : raw11192step3 = raw11192step2 := by apply Matrix.ext; unfold raw11192step3 raw11192step2; decide +kernel
      have hl : raw11192step2Labels = labelEmbedding1 ∘ raw11192step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11192step2 raw11192step2Labels raw11192step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3156 node3156Labels := by rfl

def raw11193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11193step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11193step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11193step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11193 raw11193Labels = mixedMoment B node1370 node1370Labels := by
  calc
    mixedMoment B raw11193 raw11193Labels = mixedMoment B raw11193step0 raw11193step0Labels := by
      have hz : ∀ j, raw11193 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11193step0 = (fun i j => raw11193 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11193step0 raw11193; decide +kernel
      have hl : raw11193step0Labels = raw11193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11193 raw11193Labels permutation434 hz
    mixedMoment B raw11193step0 raw11193step0Labels = mixedMoment B raw11193step1 raw11193step1Labels := by
      have ha : raw11193step1 = (fun i j => raw11193step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11193step1 raw11193step0; decide +kernel
      have hl : raw11193step1Labels = raw11193step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11193step0 raw11193step0Labels permutation50 permutation5
    mixedMoment B raw11193step1 raw11193step1Labels = mixedMoment B raw11193step2 raw11193step2Labels := by
      have ha : raw11193step2 = -raw11193step1 := by apply Matrix.ext; change ∀ i j, raw11193step2 i j = -(raw11193step1 i j); unfold raw11193step2 raw11193step1; decide +kernel
      have hl : raw11193step2Labels = raw11193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11193step2 raw11193step2Labels = mixedMoment B raw11193step3 raw11193step3Labels := by
      have ha : raw11193step3 = raw11193step2 := by apply Matrix.ext; unfold raw11193step3 raw11193step2; decide +kernel
      have hl : raw11193step2Labels = labelEmbedding1 ∘ raw11193step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11193step2 raw11193step2Labels raw11193step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1370 node1370Labels := by rfl

def raw11194 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11194step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11194 raw11194Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw11194 raw11194Labels = mixedMoment B raw11194step0 raw11194step0Labels := by
      have ha : raw11194step0 = (fun i j => raw11194 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11194step0 raw11194; decide +kernel
      have hl : raw11194step0Labels = raw11194Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11194 raw11194Labels permutation218 permutation5
    mixedMoment B raw11194step0 raw11194step0Labels = mixedMoment B raw11194step1 raw11194step1Labels := by
      have ha : raw11194step1 = -raw11194step0 := by apply Matrix.ext; change ∀ i j, raw11194step1 i j = -(raw11194step0 i j); unfold raw11194step1 raw11194step0; decide +kernel
      have hl : raw11194step1Labels = raw11194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11194step1 raw11194step1Labels = mixedMoment B raw11194step2 raw11194step2Labels := by
      have ha : raw11194step2 = raw11194step1 := by apply Matrix.ext; unfold raw11194step2 raw11194step1; decide +kernel
      have hl : raw11194step1Labels = labelEmbedding1 ∘ raw11194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11194step1 raw11194step1Labels raw11194step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3197 node3197Labels := by rfl

def raw11195 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw11195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw11195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11195step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11195step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11195 raw11195Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw11195 raw11195Labels = mixedMoment B raw11195step0 raw11195step0Labels := by
      have hz : ∀ j, raw11195 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11195step0 = (fun i j => raw11195 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11195step0 raw11195; decide +kernel
      have hl : raw11195step0Labels = raw11195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11195 raw11195Labels permutation434 hz
    mixedMoment B raw11195step0 raw11195step0Labels = mixedMoment B raw11195step1 raw11195step1Labels := by
      have ha : raw11195step1 = (fun i j => raw11195step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11195step1 raw11195step0; decide +kernel
      have hl : raw11195step1Labels = raw11195step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11195step0 raw11195step0Labels permutation50 permutation5
    mixedMoment B raw11195step1 raw11195step1Labels = mixedMoment B raw11195step2 raw11195step2Labels := by
      have ha : raw11195step2 = -raw11195step1 := by apply Matrix.ext; change ∀ i j, raw11195step2 i j = -(raw11195step1 i j); unfold raw11195step2 raw11195step1; decide +kernel
      have hl : raw11195step2Labels = raw11195step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11195step2 raw11195step2Labels = mixedMoment B raw11195step3 raw11195step3Labels := by
      have ha : raw11195step3 = raw11195step2 := by apply Matrix.ext; unfold raw11195step3 raw11195step2; decide +kernel
      have hl : raw11195step2Labels = labelEmbedding1 ∘ raw11195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11195step2 raw11195step2Labels raw11195step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3158 node3158Labels := by rfl

def raw11196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11196step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11196step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11196step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11196step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11196 raw11196Labels = mixedMoment B node1441 node1441Labels := by
  calc
    mixedMoment B raw11196 raw11196Labels = mixedMoment B raw11196step0 raw11196step0Labels := by
      have hz : ∀ j, raw11196 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11196step0 = (fun i j => raw11196 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11196step0 raw11196; decide +kernel
      have hl : raw11196step0Labels = raw11196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11196 raw11196Labels permutation434 hz
    mixedMoment B raw11196step0 raw11196step0Labels = mixedMoment B raw11196step1 raw11196step1Labels := by
      have ha : raw11196step1 = (fun i j => raw11196step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11196step1 raw11196step0; decide +kernel
      have hl : raw11196step1Labels = raw11196step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11196step0 raw11196step0Labels permutation54 permutation5
    mixedMoment B raw11196step1 raw11196step1Labels = mixedMoment B raw11196step2 raw11196step2Labels := by
      have ha : raw11196step2 = -raw11196step1 := by apply Matrix.ext; change ∀ i j, raw11196step2 i j = -(raw11196step1 i j); unfold raw11196step2 raw11196step1; decide +kernel
      have hl : raw11196step2Labels = raw11196step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11196step2 raw11196step2Labels = mixedMoment B raw11196step3 raw11196step3Labels := by
      have ha : raw11196step3 = raw11196step2 := by apply Matrix.ext; unfold raw11196step3 raw11196step2; decide +kernel
      have hl : raw11196step2Labels = labelEmbedding1 ∘ raw11196step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11196step2 raw11196step2Labels raw11196step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1441 node1441Labels := by rfl

def raw11197 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11197step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11197step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw11197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11197step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw11197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11197 raw11197Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw11197 raw11197Labels = mixedMoment B raw11197step0 raw11197step0Labels := by
      have hz : ∀ j, raw11197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11197step0 = (fun i j => raw11197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11197step0 raw11197; decide +kernel
      have hl : raw11197step0Labels = raw11197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11197 raw11197Labels permutation434 hz
    mixedMoment B raw11197step0 raw11197step0Labels = mixedMoment B raw11197step1 raw11197step1Labels := by
      have hz : ∀ j, raw11197step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11197step1 = (fun i j => raw11197step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11197step1 raw11197step0; decide +kernel
      have hl : raw11197step1Labels = raw11197step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11197step0 raw11197step0Labels permutation56 hz
    mixedMoment B raw11197step1 raw11197step1Labels = mixedMoment B raw11197step2 raw11197step2Labels := by
      have ha : raw11197step2 = (fun i j => raw11197step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11197step2 raw11197step1; decide +kernel
      have hl : raw11197step2Labels = raw11197step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11197step1 raw11197step1Labels permutation8 permutation7
    mixedMoment B raw11197step2 raw11197step2Labels = mixedMoment B raw11197step3 raw11197step3Labels := by
      have ha : raw11197step3 = raw11197step2 := by apply Matrix.ext; unfold raw11197step3 raw11197step2; decide +kernel
      have hl : raw11197step2Labels = labelEmbedding1 ∘ raw11197step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11197step2 raw11197step2Labels raw11197step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw11198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11198 raw11198Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw11198 raw11198Labels = mixedMoment B raw11198step0 raw11198step0Labels := by
      have hz : ∀ j, raw11198 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11198step0 = (fun i j => raw11198 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11198step0 raw11198; decide +kernel
      have hl : raw11198step0Labels = raw11198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11198 raw11198Labels permutation434 hz
    mixedMoment B raw11198step0 raw11198step0Labels = mixedMoment B raw11198step1 raw11198step1Labels := by
      have ha : raw11198step1 = (fun i j => raw11198step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11198step1 raw11198step0; decide +kernel
      have hl : raw11198step1Labels = raw11198step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11198step0 raw11198step0Labels permutation53 permutation4
    mixedMoment B raw11198step1 raw11198step1Labels = mixedMoment B raw11198step2 raw11198step2Labels := by
      have ha : raw11198step2 = -raw11198step1 := by apply Matrix.ext; change ∀ i j, raw11198step2 i j = -(raw11198step1 i j); unfold raw11198step2 raw11198step1; decide +kernel
      have hl : raw11198step2Labels = raw11198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1058 node1058Labels := by rfl

def raw11199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw11199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw11199step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw11199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11199 raw11199Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw11199 raw11199Labels = mixedMoment B raw11199step0 raw11199step0Labels := by
      have hz : ∀ j, raw11199 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11199step0 = (fun i j => raw11199 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11199step0 raw11199; decide +kernel
      have hl : raw11199step0Labels = raw11199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11199 raw11199Labels permutation434 hz
    mixedMoment B raw11199step0 raw11199step0Labels = mixedMoment B raw11199step1 raw11199step1Labels := by
      have ha : raw11199step1 = (fun i j => raw11199step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11199step1 raw11199step0; decide +kernel
      have hl : raw11199step1Labels = raw11199step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11199step0 raw11199step0Labels permutation51 permutation4
    mixedMoment B raw11199step1 raw11199step1Labels = mixedMoment B raw11199step2 raw11199step2Labels := by
      have ha : raw11199step2 = -raw11199step1 := by apply Matrix.ext; change ∀ i j, raw11199step2 i j = -(raw11199step1 i j); unfold raw11199step2 raw11199step1; decide +kernel
      have hl : raw11199step2Labels = raw11199step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1058 node1058Labels := by rfl

def raw11200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw11200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw11200step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11200step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11200 raw11200Labels = mixedMoment B node1057 node1057Labels := by
  calc
    mixedMoment B raw11200 raw11200Labels = mixedMoment B raw11200step0 raw11200step0Labels := by
      have hz : ∀ j, raw11200 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11200step0 = (fun i j => raw11200 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11200step0 raw11200; decide +kernel
      have hl : raw11200step0Labels = raw11200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11200 raw11200Labels permutation434 hz
    mixedMoment B raw11200step0 raw11200step0Labels = mixedMoment B raw11200step1 raw11200step1Labels := by
      have ha : raw11200step1 = (fun i j => raw11200step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11200step1 raw11200step0; decide +kernel
      have hl : raw11200step1Labels = raw11200step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11200step0 raw11200step0Labels permutation50 permutation4
    mixedMoment B raw11200step1 raw11200step1Labels = mixedMoment B raw11200step2 raw11200step2Labels := by
      have ha : raw11200step2 = -raw11200step1 := by apply Matrix.ext; change ∀ i j, raw11200step2 i j = -(raw11200step1 i j); unfold raw11200step2 raw11200step1; decide +kernel
      have hl : raw11200step2Labels = raw11200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1057 node1057Labels := by rfl

def raw11201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw11201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11201step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11201 raw11201Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw11201 raw11201Labels = mixedMoment B raw11201step0 raw11201step0Labels := by
      have hz : ∀ j, raw11201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11201step0 = (fun i j => raw11201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11201step0 raw11201; decide +kernel
      have hl : raw11201step0Labels = raw11201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11201 raw11201Labels permutation434 hz
    mixedMoment B raw11201step0 raw11201step0Labels = mixedMoment B raw11201step1 raw11201step1Labels := by
      have ha : raw11201step1 = (fun i j => raw11201step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11201step1 raw11201step0; decide +kernel
      have hl : raw11201step1Labels = raw11201step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11201step0 raw11201step0Labels permutation32 permutation4
    mixedMoment B raw11201step1 raw11201step1Labels = mixedMoment B raw11201step2 raw11201step2Labels := by
      have ha : raw11201step2 = -raw11201step1 := by apply Matrix.ext; change ∀ i j, raw11201step2 i j = -(raw11201step1 i j); unfold raw11201step2 raw11201step1; decide +kernel
      have hl : raw11201step2Labels = raw11201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw11202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11202step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11202step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11202step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11202 raw11202Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw11202 raw11202Labels = mixedMoment B raw11202step0 raw11202step0Labels := by
      have hz : ∀ j, raw11202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11202step0 = (fun i j => raw11202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11202step0 raw11202; decide +kernel
      have hl : raw11202step0Labels = raw11202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11202 raw11202Labels permutation434 hz
    mixedMoment B raw11202step0 raw11202step0Labels = mixedMoment B raw11202step1 raw11202step1Labels := by
      have ha : raw11202step1 = (fun i j => raw11202step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11202step1 raw11202step0; decide +kernel
      have hl : raw11202step1Labels = raw11202step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11202step0 raw11202step0Labels permutation44 permutation7
    mixedMoment B raw11202step1 raw11202step1Labels = mixedMoment B raw11202step2 raw11202step2Labels := by
      have ha : raw11202step2 = -raw11202step1 := by apply Matrix.ext; change ∀ i j, raw11202step2 i j = -(raw11202step1 i j); unfold raw11202step2 raw11202step1; decide +kernel
      have hl : raw11202step2Labels = raw11202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11202step2 raw11202step2Labels = mixedMoment B raw11202step3 raw11202step3Labels := by
      have ha : raw11202step3 = raw11202step2 := by apply Matrix.ext; unfold raw11202step3 raw11202step2; decide +kernel
      have hl : raw11202step2Labels = labelEmbedding10 ∘ raw11202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11202step2 raw11202step2Labels raw11202step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw11203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11203step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11203step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11203step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11203 raw11203Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw11203 raw11203Labels = mixedMoment B raw11203step0 raw11203step0Labels := by
      have hz : ∀ j, raw11203 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11203step0 = (fun i j => raw11203 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11203step0 raw11203; decide +kernel
      have hl : raw11203step0Labels = raw11203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11203 raw11203Labels permutation434 hz
    mixedMoment B raw11203step0 raw11203step0Labels = mixedMoment B raw11203step1 raw11203step1Labels := by
      have ha : raw11203step1 = (fun i j => raw11203step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11203step1 raw11203step0; decide +kernel
      have hl : raw11203step1Labels = raw11203step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11203step0 raw11203step0Labels permutation46 permutation7
    mixedMoment B raw11203step1 raw11203step1Labels = mixedMoment B raw11203step2 raw11203step2Labels := by
      have ha : raw11203step2 = -raw11203step1 := by apply Matrix.ext; change ∀ i j, raw11203step2 i j = -(raw11203step1 i j); unfold raw11203step2 raw11203step1; decide +kernel
      have hl : raw11203step2Labels = raw11203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11203step2 raw11203step2Labels = mixedMoment B raw11203step3 raw11203step3Labels := by
      have ha : raw11203step3 = raw11203step2 := by apply Matrix.ext; unfold raw11203step3 raw11203step2; decide +kernel
      have hl : raw11203step2Labels = labelEmbedding10 ∘ raw11203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11203step2 raw11203step2Labels raw11203step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw11204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11204step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11204step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11204step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11204step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11204 raw11204Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw11204 raw11204Labels = mixedMoment B raw11204step0 raw11204step0Labels := by
      have ha : raw11204step0 = (fun i j => raw11204 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11204step0 raw11204; decide +kernel
      have hl : raw11204step0Labels = raw11204Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11204 raw11204Labels permutation212 permutation7
    mixedMoment B raw11204step0 raw11204step0Labels = mixedMoment B raw11204step1 raw11204step1Labels := by
      have ha : raw11204step1 = -raw11204step0 := by apply Matrix.ext; change ∀ i j, raw11204step1 i j = -(raw11204step0 i j); unfold raw11204step1 raw11204step0; decide +kernel
      have hl : raw11204step1Labels = raw11204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11204step1 raw11204step1Labels = mixedMoment B raw11204step2 raw11204step2Labels := by
      have ha : raw11204step2 = raw11204step1 := by apply Matrix.ext; unfold raw11204step2 raw11204step1; decide +kernel
      have hl : raw11204step1Labels = labelEmbedding10 ∘ raw11204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11204step1 raw11204step1Labels raw11204step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw11205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11205step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11205step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11205step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11205step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11205step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11205step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11205 raw11205Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw11205 raw11205Labels = mixedMoment B raw11205step0 raw11205step0Labels := by
      have hz : ∀ j, raw11205 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11205step0 = (fun i j => raw11205 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11205step0 raw11205; decide +kernel
      have hl : raw11205step0Labels = raw11205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11205 raw11205Labels permutation520 hz
    mixedMoment B raw11205step0 raw11205step0Labels = mixedMoment B raw11205step1 raw11205step1Labels := by
      have hz : ∀ j, raw11205step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11205step1 = (fun i j => raw11205step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11205step1 raw11205step0; decide +kernel
      have hl : raw11205step1Labels = raw11205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11205step0 raw11205step0Labels permutation104 hz
    mixedMoment B raw11205step1 raw11205step1Labels = mixedMoment B raw11205step2 raw11205step2Labels := by
      have ha : raw11205step2 = (fun i j => raw11205step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11205step2 raw11205step1; decide +kernel
      have hl : raw11205step2Labels = raw11205step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11205step1 raw11205step1Labels permutation8 permutation7
    mixedMoment B raw11205step2 raw11205step2Labels = mixedMoment B raw11205step3 raw11205step3Labels := by
      have ha : raw11205step3 = -raw11205step2 := by apply Matrix.ext; change ∀ i j, raw11205step3 i j = -(raw11205step2 i j); unfold raw11205step3 raw11205step2; decide +kernel
      have hl : raw11205step3Labels = raw11205step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11205step3 raw11205step3Labels = mixedMoment B raw11205step4 raw11205step4Labels := by
      have ha : raw11205step4 = raw11205step3 := by apply Matrix.ext; unfold raw11205step4 raw11205step3; decide +kernel
      have hl : raw11205step3Labels = labelEmbedding10 ∘ raw11205step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11205step3 raw11205step3Labels raw11205step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw11206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11206step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11206step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11206step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11206 raw11206Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw11206 raw11206Labels = mixedMoment B raw11206step0 raw11206step0Labels := by
      have hz : ∀ j, raw11206 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11206step0 = (fun i j => raw11206 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11206step0 raw11206; decide +kernel
      have hl : raw11206step0Labels = raw11206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11206 raw11206Labels permutation434 hz
    mixedMoment B raw11206step0 raw11206step0Labels = mixedMoment B raw11206step1 raw11206step1Labels := by
      have ha : raw11206step1 = (fun i j => raw11206step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11206step1 raw11206step0; decide +kernel
      have hl : raw11206step1Labels = raw11206step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11206step0 raw11206step0Labels permutation44 permutation7
    mixedMoment B raw11206step1 raw11206step1Labels = mixedMoment B raw11206step2 raw11206step2Labels := by
      have ha : raw11206step2 = -raw11206step1 := by apply Matrix.ext; change ∀ i j, raw11206step2 i j = -(raw11206step1 i j); unfold raw11206step2 raw11206step1; decide +kernel
      have hl : raw11206step2Labels = raw11206step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11206step2 raw11206step2Labels = mixedMoment B raw11206step3 raw11206step3Labels := by
      have ha : raw11206step3 = raw11206step2 := by apply Matrix.ext; unfold raw11206step3 raw11206step2; decide +kernel
      have hl : raw11206step2Labels = labelEmbedding10 ∘ raw11206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11206step2 raw11206step2Labels raw11206step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw11207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11207step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11207 raw11207Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw11207 raw11207Labels = mixedMoment B raw11207step0 raw11207step0Labels := by
      have hz : ∀ j, raw11207 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11207step0 = (fun i j => raw11207 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11207step0 raw11207; decide +kernel
      have hl : raw11207step0Labels = raw11207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11207 raw11207Labels permutation434 hz
    mixedMoment B raw11207step0 raw11207step0Labels = mixedMoment B raw11207step1 raw11207step1Labels := by
      have ha : raw11207step1 = (fun i j => raw11207step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11207step1 raw11207step0; decide +kernel
      have hl : raw11207step1Labels = raw11207step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11207step0 raw11207step0Labels permutation40 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw11208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11208 raw11208Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw11208 raw11208Labels = mixedMoment B raw11208step0 raw11208step0Labels := by
      have hz : ∀ j, raw11208 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11208step0 = (fun i j => raw11208 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11208step0 raw11208; decide +kernel
      have hl : raw11208step0Labels = raw11208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11208 raw11208Labels permutation434 hz
    mixedMoment B raw11208step0 raw11208step0Labels = mixedMoment B raw11208step1 raw11208step1Labels := by
      have ha : raw11208step1 = (fun i j => raw11208step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11208step1 raw11208step0; decide +kernel
      have hl : raw11208step1Labels = raw11208step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11208step0 raw11208step0Labels permutation40 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw11209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11209 raw11209Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw11209 raw11209Labels = mixedMoment B raw11209step0 raw11209step0Labels := by
      have ha : raw11209step0 = (fun i j => raw11209 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11209step0 raw11209; decide +kernel
      have hl : raw11209step0Labels = raw11209Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11209 raw11209Labels permutation208 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw11210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11210step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11210 raw11210Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw11210 raw11210Labels = mixedMoment B raw11210step0 raw11210step0Labels := by
      have hz : ∀ j, raw11210 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11210step0 = (fun i j => raw11210 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11210step0 raw11210; decide +kernel
      have hl : raw11210step0Labels = raw11210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11210 raw11210Labels permutation520 hz
    mixedMoment B raw11210step0 raw11210step0Labels = mixedMoment B raw11210step1 raw11210step1Labels := by
      have hz : ∀ j, raw11210step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11210step1 = (fun i j => raw11210step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11210step1 raw11210step0; decide +kernel
      have hl : raw11210step1Labels = raw11210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11210step0 raw11210step0Labels permutation104 hz
    mixedMoment B raw11210step1 raw11210step1Labels = mixedMoment B raw11210step2 raw11210step2Labels := by
      have ha : raw11210step2 = (fun i j => raw11210step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11210step2 raw11210step1; decide +kernel
      have hl : raw11210step2Labels = raw11210step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11210step1 raw11210step1Labels permutation10 permutation2
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw11211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11211 raw11211Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw11211 raw11211Labels = mixedMoment B raw11211step0 raw11211step0Labels := by
      have hz : ∀ j, raw11211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11211step0 = (fun i j => raw11211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11211step0 raw11211; decide +kernel
      have hl : raw11211step0Labels = raw11211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11211 raw11211Labels permutation434 hz
    mixedMoment B raw11211step0 raw11211step0Labels = mixedMoment B raw11211step1 raw11211step1Labels := by
      have ha : raw11211step1 = (fun i j => raw11211step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11211step1 raw11211step0; decide +kernel
      have hl : raw11211step1Labels = raw11211step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11211step0 raw11211step0Labels permutation40 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw11212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11212 raw11212Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw11212 raw11212Labels = mixedMoment B raw11212step0 raw11212step0Labels := by
      have hz : ∀ j, raw11212 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11212step0 = (fun i j => raw11212 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11212step0 raw11212; decide +kernel
      have hl : raw11212step0Labels = raw11212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11212 raw11212Labels permutation434 hz
    mixedMoment B raw11212step0 raw11212step0Labels = mixedMoment B raw11212step1 raw11212step1Labels := by
      have ha : raw11212step1 = (fun i j => raw11212step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11212step1 raw11212step0; decide +kernel
      have hl : raw11212step1Labels = raw11212step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11212step0 raw11212step0Labels permutation34 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw11213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11213 raw11213Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw11213 raw11213Labels = mixedMoment B raw11213step0 raw11213step0Labels := by
      have hz : ∀ j, raw11213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11213step0 = (fun i j => raw11213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11213step0 raw11213; decide +kernel
      have hl : raw11213step0Labels = raw11213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11213 raw11213Labels permutation434 hz
    mixedMoment B raw11213step0 raw11213step0Labels = mixedMoment B raw11213step1 raw11213step1Labels := by
      have ha : raw11213step1 = (fun i j => raw11213step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11213step1 raw11213step0; decide +kernel
      have hl : raw11213step1Labels = raw11213step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11213step0 raw11213step0Labels permutation34 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw11214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11214 raw11214Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw11214 raw11214Labels = mixedMoment B raw11214step0 raw11214step0Labels := by
      have ha : raw11214step0 = (fun i j => raw11214 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11214step0 raw11214; decide +kernel
      have hl : raw11214step0Labels = raw11214Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11214 raw11214Labels permutation202 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw11215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11215step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11215 raw11215Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw11215 raw11215Labels = mixedMoment B raw11215step0 raw11215step0Labels := by
      have hz : ∀ j, raw11215 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11215step0 = (fun i j => raw11215 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11215step0 raw11215; decide +kernel
      have hl : raw11215step0Labels = raw11215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11215 raw11215Labels permutation520 hz
    mixedMoment B raw11215step0 raw11215step0Labels = mixedMoment B raw11215step1 raw11215step1Labels := by
      have hz : ∀ j, raw11215step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11215step1 = (fun i j => raw11215step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11215step1 raw11215step0; decide +kernel
      have hl : raw11215step1Labels = raw11215step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11215step0 raw11215step0Labels permutation104 hz
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw11216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11216 raw11216Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw11216 raw11216Labels = mixedMoment B raw11216step0 raw11216step0Labels := by
      have hz : ∀ j, raw11216 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11216step0 = (fun i j => raw11216 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11216step0 raw11216; decide +kernel
      have hl : raw11216step0Labels = raw11216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11216 raw11216Labels permutation434 hz
    mixedMoment B raw11216step0 raw11216step0Labels = mixedMoment B raw11216step1 raw11216step1Labels := by
      have ha : raw11216step1 = (fun i j => raw11216step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11216step1 raw11216step0; decide +kernel
      have hl : raw11216step1Labels = raw11216step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11216step0 raw11216step0Labels permutation34 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw11217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11217 raw11217Labels = mixedMoment B node4438 node4438Labels := by
  calc
    _ = mixedMoment B node4438 node4438Labels := by rfl

def raw11218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11218 raw11218Labels = mixedMoment B node4851 node4851Labels := by
  calc
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw11219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11219 raw11219Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw11219 raw11219Labels = mixedMoment B raw11219step0 raw11219step0Labels := by
      have ha : raw11219step0 = (fun i j => raw11219 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11219step0 raw11219; decide +kernel
      have hl : raw11219step0Labels = raw11219Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11219 raw11219Labels permutation176 permutation2
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw11220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11220 raw11220Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11220 raw11220Labels = mixedMoment B raw11220step0 raw11220step0Labels := by
      have hz : ∀ j, raw11220 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11220step0 = (fun i j => raw11220 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11220step0 raw11220; decide +kernel
      have hl : raw11220step0Labels = raw11220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11220 raw11220Labels permutation520 hz
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw11221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11221 raw11221Labels = mixedMoment B node4887 node4887Labels := by
  calc
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw11222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11222 raw11222Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw11222 raw11222Labels = mixedMoment B raw11222step0 raw11222step0Labels := by
      have hz : ∀ j, raw11222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11222step0 = (fun i j => raw11222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11222step0 raw11222; decide +kernel
      have hl : raw11222step0Labels = raw11222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11222 raw11222Labels permutation434 hz
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw11223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11223 raw11223Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw11223 raw11223Labels = mixedMoment B raw11223step0 raw11223step0Labels := by
      have hz : ∀ j, raw11223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11223step0 = (fun i j => raw11223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11223step0 raw11223; decide +kernel
      have hl : raw11223step0Labels = raw11223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11223 raw11223Labels permutation434 hz
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw11224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11224 raw11224Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw11224 raw11224Labels = mixedMoment B raw11224step0 raw11224step0Labels := by
      have hz : ∀ j, raw11224 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11224step0 = (fun i j => raw11224 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11224step0 raw11224; decide +kernel
      have hl : raw11224step0Labels = raw11224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11224 raw11224Labels permutation434 hz
    mixedMoment B raw11224step0 raw11224step0Labels = mixedMoment B raw11224step1 raw11224step1Labels := by
      have ha : raw11224step1 = (fun i j => raw11224step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11224step1 raw11224step0; decide +kernel
      have hl : raw11224step1Labels = raw11224step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11224step0 raw11224step0Labels permutation38 permutation2
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw11225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11225 raw11225Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw11225 raw11225Labels = mixedMoment B raw11225step0 raw11225step0Labels := by
      have ha : raw11225step0 = (fun i j => raw11225 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11225step0 raw11225; decide +kernel
      have hl : raw11225step0Labels = raw11225Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11225 raw11225Labels permutation200 permutation2
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw11226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw11226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11226 raw11226Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw11226 raw11226Labels = mixedMoment B raw11226step0 raw11226step0Labels := by
      have hz : ∀ j, raw11226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11226step0 = (fun i j => raw11226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11226step0 raw11226; decide +kernel
      have hl : raw11226step0Labels = raw11226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11226 raw11226Labels permutation434 hz
    mixedMoment B raw11226step0 raw11226step0Labels = mixedMoment B raw11226step1 raw11226step1Labels := by
      have ha : raw11226step1 = (fun i j => raw11226step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11226step1 raw11226step0; decide +kernel
      have hl : raw11226step1Labels = raw11226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11226step0 raw11226step0Labels permutation33 permutation2
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw11227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11227 raw11227Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw11227 raw11227Labels = mixedMoment B raw11227step0 raw11227step0Labels := by
      have hz : ∀ j, raw11227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11227step0 = (fun i j => raw11227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11227step0 raw11227; decide +kernel
      have hl : raw11227step0Labels = raw11227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11227 raw11227Labels permutation434 hz
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw11228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11228 raw11228Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw11228 raw11228Labels = mixedMoment B raw11228step0 raw11228step0Labels := by
      have hz : ∀ j, raw11228 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11228step0 = (fun i j => raw11228 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11228step0 raw11228; decide +kernel
      have hl : raw11228step0Labels = raw11228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11228 raw11228Labels permutation434 hz
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw11229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11229 raw11229Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw11229 raw11229Labels = mixedMoment B raw11229step0 raw11229step0Labels := by
      have hz : ∀ j, raw11229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11229step0 = (fun i j => raw11229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11229step0 raw11229; decide +kernel
      have hl : raw11229step0Labels = raw11229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11229 raw11229Labels permutation434 hz
    mixedMoment B raw11229step0 raw11229step0Labels = mixedMoment B raw11229step1 raw11229step1Labels := by
      have ha : raw11229step1 = (fun i j => raw11229step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11229step1 raw11229step0; decide +kernel
      have hl : raw11229step1Labels = raw11229step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11229step0 raw11229step0Labels permutation38 permutation2
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw11230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11230 raw11230Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw11230 raw11230Labels = mixedMoment B raw11230step0 raw11230step0Labels := by
      have ha : raw11230step0 = (fun i j => raw11230 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11230step0 raw11230; decide +kernel
      have hl : raw11230step0Labels = raw11230Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11230 raw11230Labels permutation200 permutation2
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw11231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw11231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw11231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11231 raw11231Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw11231 raw11231Labels = mixedMoment B raw11231step0 raw11231step0Labels := by
      have hz : ∀ j, raw11231 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11231step0 = (fun i j => raw11231 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11231step0 raw11231; decide +kernel
      have hl : raw11231step0Labels = raw11231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11231 raw11231Labels permutation520 hz
    mixedMoment B raw11231step0 raw11231step0Labels = mixedMoment B raw11231step1 raw11231step1Labels := by
      have hz : ∀ j, raw11231step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11231step1 = (fun i j => raw11231step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11231step1 raw11231step0; decide +kernel
      have hl : raw11231step1Labels = raw11231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11231step0 raw11231step0Labels permutation104 hz
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw11232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11232Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11232step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11232 raw11232Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw11232 raw11232Labels = mixedMoment B raw11232step0 raw11232step0Labels := by
      have hz : ∀ j, raw11232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11232step0 = (fun i j => raw11232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11232step0 raw11232; decide +kernel
      have hl : raw11232step0Labels = raw11232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11232 raw11232Labels permutation434 hz
    mixedMoment B raw11232step0 raw11232step0Labels = mixedMoment B raw11232step1 raw11232step1Labels := by
      have ha : raw11232step1 = (fun i j => raw11232step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11232step1 raw11232step0; decide +kernel
      have hl : raw11232step1Labels = raw11232step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11232step0 raw11232step0Labels permutation49 permutation6
    mixedMoment B raw11232step1 raw11232step1Labels = mixedMoment B raw11232step2 raw11232step2Labels := by
      have ha : raw11232step2 = -raw11232step1 := by apply Matrix.ext; change ∀ i j, raw11232step2 i j = -(raw11232step1 i j); unfold raw11232step2 raw11232step1; decide +kernel
      have hl : raw11232step2Labels = raw11232step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw11233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11233Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11233step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11233step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11233 raw11233Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw11233 raw11233Labels = mixedMoment B raw11233step0 raw11233step0Labels := by
      have hz : ∀ j, raw11233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11233step0 = (fun i j => raw11233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11233step0 raw11233; decide +kernel
      have hl : raw11233step0Labels = raw11233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11233 raw11233Labels permutation434 hz
    mixedMoment B raw11233step0 raw11233step0Labels = mixedMoment B raw11233step1 raw11233step1Labels := by
      have ha : raw11233step1 = (fun i j => raw11233step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11233step1 raw11233step0; decide +kernel
      have hl : raw11233step1Labels = raw11233step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11233step0 raw11233step0Labels permutation48 permutation6
    mixedMoment B raw11233step1 raw11233step1Labels = mixedMoment B raw11233step2 raw11233step2Labels := by
      have ha : raw11233step2 = -raw11233step1 := by apply Matrix.ext; change ∀ i j, raw11233step2 i j = -(raw11233step1 i j); unfold raw11233step2 raw11233step1; decide +kernel
      have hl : raw11233step2Labels = raw11233step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw11234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11234Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw11234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11234step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11234 raw11234Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw11234 raw11234Labels = mixedMoment B raw11234step0 raw11234step0Labels := by
      have ha : raw11234step0 = (fun i j => raw11234 (permutation238 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11234step0 raw11234; decide +kernel
      have hl : raw11234step0Labels = raw11234Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11234 raw11234Labels permutation238 permutation6
    mixedMoment B raw11234step0 raw11234step0Labels = mixedMoment B raw11234step1 raw11234step1Labels := by
      have ha : raw11234step1 = -raw11234step0 := by apply Matrix.ext; change ∀ i j, raw11234step1 i j = -(raw11234step0 i j); unfold raw11234step1 raw11234step0; decide +kernel
      have hl : raw11234step1Labels = raw11234step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3085 node3085Labels := by rfl

def raw11235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11235Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11235step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11235step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11235step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw11235step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11235step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11235step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11235 raw11235Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw11235 raw11235Labels = mixedMoment B raw11235step0 raw11235step0Labels := by
      have hz : ∀ j, raw11235 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11235step0 = (fun i j => raw11235 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11235step0 raw11235; decide +kernel
      have hl : raw11235step0Labels = raw11235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11235 raw11235Labels permutation520 hz
    mixedMoment B raw11235step0 raw11235step0Labels = mixedMoment B raw11235step1 raw11235step1Labels := by
      have hz : ∀ j, raw11235step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11235step1 = (fun i j => raw11235step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11235step1 raw11235step0; decide +kernel
      have hl : raw11235step1Labels = raw11235step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11235step0 raw11235step0Labels permutation104 hz
    mixedMoment B raw11235step1 raw11235step1Labels = mixedMoment B raw11235step2 raw11235step2Labels := by
      have ha : raw11235step2 = (fun i j => raw11235step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11235step2 raw11235step1; decide +kernel
      have hl : raw11235step2Labels = raw11235step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11235step1 raw11235step1Labels permutation12 permutation6
    mixedMoment B raw11235step2 raw11235step2Labels = mixedMoment B raw11235step3 raw11235step3Labels := by
      have ha : raw11235step3 = -raw11235step2 := by apply Matrix.ext; change ∀ i j, raw11235step3 i j = -(raw11235step2 i j); unfold raw11235step3 raw11235step2; decide +kernel
      have hl : raw11235step3Labels = raw11235step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw11236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11236Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11236step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11236step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11236step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11236 raw11236Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw11236 raw11236Labels = mixedMoment B raw11236step0 raw11236step0Labels := by
      have hz : ∀ j, raw11236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11236step0 = (fun i j => raw11236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11236step0 raw11236; decide +kernel
      have hl : raw11236step0Labels = raw11236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11236 raw11236Labels permutation434 hz
    mixedMoment B raw11236step0 raw11236step0Labels = mixedMoment B raw11236step1 raw11236step1Labels := by
      have ha : raw11236step1 = (fun i j => raw11236step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11236step1 raw11236step0; decide +kernel
      have hl : raw11236step1Labels = raw11236step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11236step0 raw11236step0Labels permutation48 permutation6
    mixedMoment B raw11236step1 raw11236step1Labels = mixedMoment B raw11236step2 raw11236step2Labels := by
      have ha : raw11236step2 = -raw11236step1 := by apply Matrix.ext; change ∀ i j, raw11236step2 i j = -(raw11236step1 i j); unfold raw11236step2 raw11236step1; decide +kernel
      have hl : raw11236step2Labels = raw11236step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw11237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11237Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11237step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11237step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11237 raw11237Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw11237 raw11237Labels = mixedMoment B raw11237step0 raw11237step0Labels := by
      have hz : ∀ j, raw11237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11237step0 = (fun i j => raw11237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11237step0 raw11237; decide +kernel
      have hl : raw11237step0Labels = raw11237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11237 raw11237Labels permutation434 hz
    mixedMoment B raw11237step0 raw11237step0Labels = mixedMoment B raw11237step1 raw11237step1Labels := by
      have ha : raw11237step1 = (fun i j => raw11237step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11237step1 raw11237step0; decide +kernel
      have hl : raw11237step1Labels = raw11237step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11237step0 raw11237step0Labels permutation38 permutation3
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw11238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11238Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11238step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11238 raw11238Labels = mixedMoment B node3184 node3184Labels := by
  calc
    mixedMoment B raw11238 raw11238Labels = mixedMoment B raw11238step0 raw11238step0Labels := by
      have hz : ∀ j, raw11238 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11238step0 = (fun i j => raw11238 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11238step0 raw11238; decide +kernel
      have hl : raw11238step0Labels = raw11238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11238 raw11238Labels permutation434 hz
    mixedMoment B raw11238step0 raw11238step0Labels = mixedMoment B raw11238step1 raw11238step1Labels := by
      have ha : raw11238step1 = (fun i j => raw11238step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11238step1 raw11238step0; decide +kernel
      have hl : raw11238step1Labels = raw11238step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11238step0 raw11238step0Labels permutation38 permutation3
    _ = mixedMoment B node3184 node3184Labels := by rfl

def raw11239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11239 raw11239Labels = mixedMoment B node3204 node3204Labels := by
  calc
    mixedMoment B raw11239 raw11239Labels = mixedMoment B raw11239step0 raw11239step0Labels := by
      have ha : raw11239step0 = (fun i j => raw11239 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11239step0 raw11239; decide +kernel
      have hl : raw11239step0Labels = raw11239Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11239 raw11239Labels permutation206 permutation3
    _ = mixedMoment B node3204 node3204Labels := by rfl

def raw11240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11240step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw11240step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11240step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw11240step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11240 raw11240Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw11240 raw11240Labels = mixedMoment B raw11240step0 raw11240step0Labels := by
      have hz : ∀ j, raw11240 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11240step0 = (fun i j => raw11240 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11240step0 raw11240; decide +kernel
      have hl : raw11240step0Labels = raw11240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11240 raw11240Labels permutation520 hz
    mixedMoment B raw11240step0 raw11240step0Labels = mixedMoment B raw11240step1 raw11240step1Labels := by
      have hz : ∀ j, raw11240step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11240step1 = (fun i j => raw11240step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11240step1 raw11240step0; decide +kernel
      have hl : raw11240step1Labels = raw11240step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11240step0 raw11240step0Labels permutation104 hz
    mixedMoment B raw11240step1 raw11240step1Labels = mixedMoment B raw11240step2 raw11240step2Labels := by
      have ha : raw11240step2 = (fun i j => raw11240step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11240step2 raw11240step1; decide +kernel
      have hl : raw11240step2Labels = raw11240step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11240step1 raw11240step1Labels permutation10 permutation3
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw11241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11241step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11241 raw11241Labels = mixedMoment B node3228 node3228Labels := by
  calc
    mixedMoment B raw11241 raw11241Labels = mixedMoment B raw11241step0 raw11241step0Labels := by
      have hz : ∀ j, raw11241 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11241step0 = (fun i j => raw11241 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11241step0 raw11241; decide +kernel
      have hl : raw11241step0Labels = raw11241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11241 raw11241Labels permutation434 hz
    mixedMoment B raw11241step0 raw11241step0Labels = mixedMoment B raw11241step1 raw11241step1Labels := by
      have ha : raw11241step1 = (fun i j => raw11241step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11241step1 raw11241step0; decide +kernel
      have hl : raw11241step1Labels = raw11241step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11241step0 raw11241step0Labels permutation39 permutation3
    _ = mixedMoment B node3228 node3228Labels := by rfl

def raw11242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11242step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11242 raw11242Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw11242 raw11242Labels = mixedMoment B raw11242step0 raw11242step0Labels := by
      have hz : ∀ j, raw11242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11242step0 = (fun i j => raw11242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11242step0 raw11242; decide +kernel
      have hl : raw11242step0Labels = raw11242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11242 raw11242Labels permutation434 hz
    mixedMoment B raw11242step0 raw11242step0Labels = mixedMoment B raw11242step1 raw11242step1Labels := by
      have ha : raw11242step1 = (fun i j => raw11242step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11242step1 raw11242step0; decide +kernel
      have hl : raw11242step1Labels = raw11242step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11242step0 raw11242step0Labels permutation32 permutation3
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw11243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11243step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11243 raw11243Labels = mixedMoment B node3184 node3184Labels := by
  calc
    mixedMoment B raw11243 raw11243Labels = mixedMoment B raw11243step0 raw11243step0Labels := by
      have hz : ∀ j, raw11243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11243step0 = (fun i j => raw11243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11243step0 raw11243; decide +kernel
      have hl : raw11243step0Labels = raw11243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11243 raw11243Labels permutation434 hz
    mixedMoment B raw11243step0 raw11243step0Labels = mixedMoment B raw11243step1 raw11243step1Labels := by
      have ha : raw11243step1 = (fun i j => raw11243step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11243step1 raw11243step0; decide +kernel
      have hl : raw11243step1Labels = raw11243step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11243step0 raw11243step0Labels permutation32 permutation3
    _ = mixedMoment B node3184 node3184Labels := by rfl

def raw11244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11244step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11244 raw11244Labels = mixedMoment B node3204 node3204Labels := by
  calc
    mixedMoment B raw11244 raw11244Labels = mixedMoment B raw11244step0 raw11244step0Labels := by
      have ha : raw11244step0 = (fun i j => raw11244 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11244step0 raw11244; decide +kernel
      have hl : raw11244step0Labels = raw11244Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11244 raw11244Labels permutation200 permutation3
    _ = mixedMoment B node3204 node3204Labels := by rfl

def raw11245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw11245step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11245step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw11245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11245 raw11245Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw11245 raw11245Labels = mixedMoment B raw11245step0 raw11245step0Labels := by
      have hz : ∀ j, raw11245 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11245step0 = (fun i j => raw11245 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11245step0 raw11245; decide +kernel
      have hl : raw11245step0Labels = raw11245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11245 raw11245Labels permutation520 hz
    mixedMoment B raw11245step0 raw11245step0Labels = mixedMoment B raw11245step1 raw11245step1Labels := by
      have hz : ∀ j, raw11245step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11245step1 = (fun i j => raw11245step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11245step1 raw11245step0; decide +kernel
      have hl : raw11245step1Labels = raw11245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11245step0 raw11245step0Labels permutation104 hz
    mixedMoment B raw11245step1 raw11245step1Labels = mixedMoment B raw11245step2 raw11245step2Labels := by
      have ha : raw11245step2 = (fun i j => raw11245step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11245step2 raw11245step1; decide +kernel
      have hl : raw11245step2Labels = raw11245step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11245step1 raw11245step1Labels permutation8 permutation3
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw11246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw11246step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11246 raw11246Labels = mixedMoment B node3228 node3228Labels := by
  calc
    mixedMoment B raw11246 raw11246Labels = mixedMoment B raw11246step0 raw11246step0Labels := by
      have hz : ∀ j, raw11246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11246step0 = (fun i j => raw11246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11246step0 raw11246; decide +kernel
      have hl : raw11246step0Labels = raw11246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11246 raw11246Labels permutation434 hz
    mixedMoment B raw11246step0 raw11246step0Labels = mixedMoment B raw11246step1 raw11246step1Labels := by
      have ha : raw11246step1 = (fun i j => raw11246step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11246step1 raw11246step0; decide +kernel
      have hl : raw11246step1Labels = raw11246step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11246step0 raw11246step0Labels permutation33 permutation3
    _ = mixedMoment B node3228 node3228Labels := by rfl

def raw11247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11247step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11247 raw11247Labels = mixedMoment B node1386 node1386Labels := by
  calc
    mixedMoment B raw11247 raw11247Labels = mixedMoment B raw11247step0 raw11247step0Labels := by
      have ha : raw11247step0 = (fun i j => raw11247 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11247step0 raw11247; decide +kernel
      have hl : raw11247step0Labels = raw11247Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11247 raw11247Labels permutation152 permutation3
    _ = mixedMoment B node1386 node1386Labels := by rfl

def raw11248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11248 raw11248Labels = mixedMoment B node3172 node3172Labels := by
  calc
    mixedMoment B raw11248 raw11248Labels = mixedMoment B raw11248step0 raw11248step0Labels := by
      have ha : raw11248step0 = (fun i j => raw11248 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11248step0 raw11248; decide +kernel
      have hl : raw11248step0Labels = raw11248Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11248 raw11248Labels permutation152 permutation3
    _ = mixedMoment B node3172 node3172Labels := by rfl

def raw11249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11249 raw11249Labels = mixedMoment B node3172 node3172Labels := by
  calc
    mixedMoment B raw11249 raw11249Labels = mixedMoment B raw11249step0 raw11249step0Labels := by
      have ha : raw11249step0 = (fun i j => raw11249 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11249step0 raw11249; decide +kernel
      have hl : raw11249step0Labels = raw11249Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11249 raw11249Labels permutation176 permutation3
    _ = mixedMoment B node3172 node3172Labels := by rfl

def raw11250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw11250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11250 raw11250Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw11250 raw11250Labels = mixedMoment B raw11250step0 raw11250step0Labels := by
      have hz : ∀ j, raw11250 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11250step0 = (fun i j => raw11250 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11250step0 raw11250; decide +kernel
      have hl : raw11250step0Labels = raw11250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11250 raw11250Labels permutation520 hz
    mixedMoment B raw11250step0 raw11250step0Labels = mixedMoment B raw11250step1 raw11250step1Labels := by
      have ha : raw11250step1 = (fun i j => raw11250step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11250step1 raw11250step0; decide +kernel
      have hl : raw11250step1Labels = raw11250step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11250step0 raw11250step0Labels permutation32 permutation3
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw11251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11251 raw11251Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw11251 raw11251Labels = mixedMoment B raw11251step0 raw11251step0Labels := by
      have ha : raw11251step0 = (fun i j => raw11251 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11251step0 raw11251; decide +kernel
      have hl : raw11251step0Labels = raw11251Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11251 raw11251Labels permutation156 permutation3
    _ = mixedMoment B node3226 node3226Labels := by rfl

def raw11252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw11252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11252 raw11252Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw11252 raw11252Labels = mixedMoment B raw11252step0 raw11252step0Labels := by
      have hz : ∀ j, raw11252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11252step0 = (fun i j => raw11252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11252step0 raw11252; decide +kernel
      have hl : raw11252step0Labels = raw11252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11252 raw11252Labels permutation434 hz
    mixedMoment B raw11252step0 raw11252step0Labels = mixedMoment B raw11252step1 raw11252step1Labels := by
      have ha : raw11252step1 = (fun i j => raw11252step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11252step1 raw11252step0; decide +kernel
      have hl : raw11252step1Labels = raw11252step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11252step0 raw11252step0Labels permutation33 permutation3
    _ = mixedMoment B node1391 node1391Labels := by rfl

def raw11253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11253step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw11253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11253 raw11253Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw11253 raw11253Labels = mixedMoment B raw11253step0 raw11253step0Labels := by
      have hz : ∀ j, raw11253 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11253step0 = (fun i j => raw11253 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11253step0 raw11253; decide +kernel
      have hl : raw11253step0Labels = raw11253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11253 raw11253Labels permutation434 hz
    mixedMoment B raw11253step0 raw11253step0Labels = mixedMoment B raw11253step1 raw11253step1Labels := by
      have ha : raw11253step1 = (fun i j => raw11253step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11253step1 raw11253step0; decide +kernel
      have hl : raw11253step1Labels = raw11253step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11253step0 raw11253step0Labels permutation33 permutation3
    _ = mixedMoment B node3174 node3174Labels := by rfl

def raw11254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw11254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11254 raw11254Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw11254 raw11254Labels = mixedMoment B raw11254step0 raw11254step0Labels := by
      have hz : ∀ j, raw11254 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11254step0 = (fun i j => raw11254 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11254step0 raw11254; decide +kernel
      have hl : raw11254step0Labels = raw11254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11254 raw11254Labels permutation434 hz
    mixedMoment B raw11254step0 raw11254step0Labels = mixedMoment B raw11254step1 raw11254step1Labels := by
      have ha : raw11254step1 = (fun i j => raw11254step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11254step1 raw11254step0; decide +kernel
      have hl : raw11254step1Labels = raw11254step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11254step0 raw11254step0Labels permutation39 permutation3
    _ = mixedMoment B node3174 node3174Labels := by rfl

def raw11255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw11255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw11255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11255 raw11255Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw11255 raw11255Labels = mixedMoment B raw11255step0 raw11255step0Labels := by
      have ha : raw11255step0 = (fun i j => raw11255 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11255step0 raw11255; decide +kernel
      have hl : raw11255step0Labels = raw11255Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11255 raw11255Labels permutation201 permutation3
    _ = mixedMoment B node3199 node3199Labels := by rfl

def raw11256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw11256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw11256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11256 raw11256Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw11256 raw11256Labels = mixedMoment B raw11256step0 raw11256step0Labels := by
      have hz : ∀ j, raw11256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11256step0 = (fun i j => raw11256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11256step0 raw11256; decide +kernel
      have hl : raw11256step0Labels = raw11256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11256 raw11256Labels permutation434 hz
    mixedMoment B raw11256step0 raw11256step0Labels = mixedMoment B raw11256step1 raw11256step1Labels := by
      have ha : raw11256step1 = (fun i j => raw11256step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11256step1 raw11256step0; decide +kernel
      have hl : raw11256step1Labels = raw11256step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11256step0 raw11256step0Labels permutation48 permutation6
    mixedMoment B raw11256step1 raw11256step1Labels = mixedMoment B raw11256step2 raw11256step2Labels := by
      have ha : raw11256step2 = -raw11256step1 := by apply Matrix.ext; change ∀ i j, raw11256step2 i j = -(raw11256step1 i j); unfold raw11256step2 raw11256step1; decide +kernel
      have hl : raw11256step2Labels = raw11256step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw11257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11257step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw11257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11257 raw11257Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw11257 raw11257Labels = mixedMoment B raw11257step0 raw11257step0Labels := by
      have hz : ∀ j, raw11257 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11257step0 = (fun i j => raw11257 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11257step0 raw11257; decide +kernel
      have hl : raw11257step0Labels = raw11257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11257 raw11257Labels permutation434 hz
    mixedMoment B raw11257step0 raw11257step0Labels = mixedMoment B raw11257step1 raw11257step1Labels := by
      have ha : raw11257step1 = (fun i j => raw11257step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11257step1 raw11257step0; decide +kernel
      have hl : raw11257step1Labels = raw11257step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11257step0 raw11257step0Labels permutation32 permutation3
    _ = mixedMoment B node1388 node1388Labels := by rfl

def raw11258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw11258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11258 raw11258Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw11258 raw11258Labels = mixedMoment B raw11258step0 raw11258step0Labels := by
      have hz : ∀ j, raw11258 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11258step0 = (fun i j => raw11258 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11258step0 raw11258; decide +kernel
      have hl : raw11258step0Labels = raw11258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11258 raw11258Labels permutation434 hz
    mixedMoment B raw11258step0 raw11258step0Labels = mixedMoment B raw11258step1 raw11258step1Labels := by
      have ha : raw11258step1 = (fun i j => raw11258step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11258step1 raw11258step0; decide +kernel
      have hl : raw11258step1Labels = raw11258step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11258step0 raw11258step0Labels permutation151 permutation3
    mixedMoment B raw11258step1 raw11258step1Labels = mixedMoment B raw11258step2 raw11258step2Labels := by
      have ha : raw11258step2 = -raw11258step1 := by apply Matrix.ext; change ∀ i j, raw11258step2 i j = -(raw11258step1 i j); unfold raw11258step2 raw11258step1; decide +kernel
      have hl : raw11258step2Labels = raw11258step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw11259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11259step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw11259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11259step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11259 raw11259Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw11259 raw11259Labels = mixedMoment B raw11259step0 raw11259step0Labels := by
      have hz : ∀ j, raw11259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11259step0 = (fun i j => raw11259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11259step0 raw11259; decide +kernel
      have hl : raw11259step0Labels = raw11259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11259 raw11259Labels permutation434 hz
    mixedMoment B raw11259step0 raw11259step0Labels = mixedMoment B raw11259step1 raw11259step1Labels := by
      have ha : raw11259step1 = (fun i j => raw11259step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11259step1 raw11259step0; decide +kernel
      have hl : raw11259step1Labels = raw11259step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11259step0 raw11259step0Labels permutation149 permutation3
    mixedMoment B raw11259step1 raw11259step1Labels = mixedMoment B raw11259step2 raw11259step2Labels := by
      have ha : raw11259step2 = -raw11259step1 := by apply Matrix.ext; change ∀ i j, raw11259step2 i j = -(raw11259step1 i j); unfold raw11259step2 raw11259step1; decide +kernel
      have hl : raw11259step2Labels = raw11259step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw11260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw11260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw11260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11260 raw11260Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw11260 raw11260Labels = mixedMoment B raw11260step0 raw11260step0Labels := by
      have ha : raw11260step0 = (fun i j => raw11260 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11260step0 raw11260; decide +kernel
      have hl : raw11260step0Labels = raw11260Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11260 raw11260Labels permutation674 permutation3
    mixedMoment B raw11260step0 raw11260step0Labels = mixedMoment B raw11260step1 raw11260step1Labels := by
      have ha : raw11260step1 = -raw11260step0 := by apply Matrix.ext; change ∀ i j, raw11260step1 i j = -(raw11260step0 i j); unfold raw11260step1 raw11260step0; decide +kernel
      have hl : raw11260step1Labels = raw11260step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw11261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw11261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw11261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw11261step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw11261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11261step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw11261step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11261 raw11261Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw11261 raw11261Labels = mixedMoment B raw11261step0 raw11261step0Labels := by
      have hz : ∀ j, raw11261 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11261step0 = (fun i j => raw11261 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11261step0 raw11261; decide +kernel
      have hl : raw11261step0Labels = raw11261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11261 raw11261Labels permutation520 hz
    mixedMoment B raw11261step0 raw11261step0Labels = mixedMoment B raw11261step1 raw11261step1Labels := by
      have hz : ∀ j, raw11261step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11261step1 = (fun i j => raw11261step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11261step1 raw11261step0; decide +kernel
      have hl : raw11261step1Labels = raw11261step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11261step0 raw11261step0Labels permutation104 hz
    mixedMoment B raw11261step1 raw11261step1Labels = mixedMoment B raw11261step2 raw11261step2Labels := by
      have ha : raw11261step2 = (fun i j => raw11261step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11261step2 raw11261step1; decide +kernel
      have hl : raw11261step2Labels = raw11261step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11261step1 raw11261step1Labels permutation29 permutation3
    mixedMoment B raw11261step2 raw11261step2Labels = mixedMoment B raw11261step3 raw11261step3Labels := by
      have ha : raw11261step3 = -raw11261step2 := by apply Matrix.ext; change ∀ i j, raw11261step3 i j = -(raw11261step2 i j); unfold raw11261step3 raw11261step2; decide +kernel
      have hl : raw11261step3Labels = raw11261step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw11262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11262step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11262step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11262step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11262step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11262step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11262 raw11262Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw11262 raw11262Labels = mixedMoment B raw11262step0 raw11262step0Labels := by
      have hz : ∀ j, raw11262 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11262step0 = (fun i j => raw11262 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11262step0 raw11262; decide +kernel
      have hl : raw11262step0Labels = raw11262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11262 raw11262Labels permutation434 hz
    mixedMoment B raw11262step0 raw11262step0Labels = mixedMoment B raw11262step1 raw11262step1Labels := by
      have ha : raw11262step1 = (fun i j => raw11262step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11262step1 raw11262step0; decide +kernel
      have hl : raw11262step1Labels = raw11262step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11262step0 raw11262step0Labels permutation44 permutation7
    mixedMoment B raw11262step1 raw11262step1Labels = mixedMoment B raw11262step2 raw11262step2Labels := by
      have ha : raw11262step2 = -raw11262step1 := by apply Matrix.ext; change ∀ i j, raw11262step2 i j = -(raw11262step1 i j); unfold raw11262step2 raw11262step1; decide +kernel
      have hl : raw11262step2Labels = raw11262step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11262step2 raw11262step2Labels = mixedMoment B raw11262step3 raw11262step3Labels := by
      have ha : raw11262step3 = raw11262step2 := by apply Matrix.ext; unfold raw11262step3 raw11262step2; decide +kernel
      have hl : raw11262step2Labels = labelEmbedding1 ∘ raw11262step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11262step2 raw11262step2Labels raw11262step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw11263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw11263Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11263step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw11263step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11263step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11263step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11263step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11263 raw11263Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw11263 raw11263Labels = mixedMoment B raw11263step0 raw11263step0Labels := by
      have hz : ∀ j, raw11263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11263step0 = (fun i j => raw11263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11263step0 raw11263; decide +kernel
      have hl : raw11263step0Labels = raw11263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11263 raw11263Labels permutation434 hz
    mixedMoment B raw11263step0 raw11263step0Labels = mixedMoment B raw11263step1 raw11263step1Labels := by
      have ha : raw11263step1 = (fun i j => raw11263step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11263step1 raw11263step0; decide +kernel
      have hl : raw11263step1Labels = raw11263step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11263step0 raw11263step0Labels permutation46 permutation7
    mixedMoment B raw11263step1 raw11263step1Labels = mixedMoment B raw11263step2 raw11263step2Labels := by
      have ha : raw11263step2 = -raw11263step1 := by apply Matrix.ext; change ∀ i j, raw11263step2 i j = -(raw11263step1 i j); unfold raw11263step2 raw11263step1; decide +kernel
      have hl : raw11263step2Labels = raw11263step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11263step2 raw11263step2Labels = mixedMoment B raw11263step3 raw11263step3Labels := by
      have ha : raw11263step3 = raw11263step2 := by apply Matrix.ext; unfold raw11263step3 raw11263step2; decide +kernel
      have hl : raw11263step2Labels = labelEmbedding1 ∘ raw11263step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11263step2 raw11263step2Labels raw11263step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
