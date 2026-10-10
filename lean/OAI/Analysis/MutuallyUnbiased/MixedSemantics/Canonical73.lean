import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9344 raw9344Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw9344 raw9344Labels = mixedMoment B raw9344step0 raw9344step0Labels := by
      have hz : ∀ j, raw9344 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9344step0 = (fun i j => raw9344 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9344step0 raw9344; decide +kernel
      have hl : raw9344step0Labels = raw9344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9344 raw9344Labels permutation265 hz
    mixedMoment B raw9344step0 raw9344step0Labels = mixedMoment B raw9344step1 raw9344step1Labels := by
      have ha : raw9344step1 = (fun i j => raw9344step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9344step1 raw9344step0; decide +kernel
      have hl : raw9344step1Labels = raw9344step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9344step0 raw9344step0Labels permutation38 permutation2
    _ = mixedMoment B node1270 node1270Labels := by rfl

def raw9345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9345 raw9345Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw9345 raw9345Labels = mixedMoment B raw9345step0 raw9345step0Labels := by
      have hz : ∀ j, raw9345 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9345step0 = (fun i j => raw9345 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9345step0 raw9345; decide +kernel
      have hl : raw9345step0Labels = raw9345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9345 raw9345Labels permutation265 hz
    _ = mixedMoment B node1270 node1270Labels := by rfl

def raw9346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw9346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9346 raw9346Labels = mixedMoment B node1253 node1253Labels := by
  calc
    mixedMoment B raw9346 raw9346Labels = mixedMoment B raw9346step0 raw9346step0Labels := by
      have hz : ∀ j, raw9346 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9346step0 = (fun i j => raw9346 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9346step0 raw9346; decide +kernel
      have hl : raw9346step0Labels = raw9346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9346 raw9346Labels permutation265 hz
    mixedMoment B raw9346step0 raw9346step0Labels = mixedMoment B raw9346step1 raw9346step1Labels := by
      have ha : raw9346step1 = (fun i j => raw9346step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9346step1 raw9346step0; decide +kernel
      have hl : raw9346step1Labels = raw9346step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9346step0 raw9346step0Labels permutation33 permutation2
    _ = mixedMoment B node1253 node1253Labels := by rfl

def raw9347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9347 raw9347Labels = mixedMoment B node1252 node1252Labels := by
  calc
    mixedMoment B raw9347 raw9347Labels = mixedMoment B raw9347step0 raw9347step0Labels := by
      have hz : ∀ j, raw9347 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9347step0 = (fun i j => raw9347 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9347step0 raw9347; decide +kernel
      have hl : raw9347step0Labels = raw9347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9347 raw9347Labels permutation265 hz
    _ = mixedMoment B node1252 node1252Labels := by rfl

def raw9348 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]
def raw9348Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9348step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]
def raw9348step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9348step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw9348step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical9348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9348 raw9348Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9348 raw9348Labels = mixedMoment B raw9348step0 raw9348step0Labels := by
      have hz : ∀ j, raw9348 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9348step0 = (fun i j => raw9348 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9348step0 raw9348; decide +kernel
      have hl : raw9348step0Labels = raw9348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9348 raw9348Labels permutation265 hz
    mixedMoment B raw9348step0 raw9348step0Labels = mixedMoment B raw9348step1 raw9348step1Labels := by
      have ha : raw9348step1 = (fun i j => raw9348step0 (permutation50 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9348step1 raw9348step0; decide +kernel
      have hl : raw9348step1Labels = raw9348step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9348step0 raw9348step0Labels permutation50 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw9349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw9349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9349 raw9349Labels = mixedMoment B node2625 node2625Labels := by
  calc
    mixedMoment B raw9349 raw9349Labels = mixedMoment B raw9349step0 raw9349step0Labels := by
      have ha : raw9349step0 = (fun i j => raw9349 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9349step0 raw9349; decide +kernel
      have hl : raw9349step0Labels = raw9349Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9349 raw9349Labels permutation182 permutation2
    _ = mixedMoment B node2625 node2625Labels := by rfl

def raw9350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw9350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9350 raw9350Labels = mixedMoment B node2625 node2625Labels := by
  calc
    mixedMoment B raw9350 raw9350Labels = mixedMoment B raw9350step0 raw9350step0Labels := by
      have ha : raw9350step0 = (fun i j => raw9350 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9350step0 raw9350; decide +kernel
      have hl : raw9350step0Labels = raw9350Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9350 raw9350Labels permutation206 permutation2
    _ = mixedMoment B node2625 node2625Labels := by rfl

def raw9351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -3, 1]]
def raw9351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9351 raw9351Labels = mixedMoment B node2746 node2746Labels := by
  calc
    mixedMoment B raw9351 raw9351Labels = mixedMoment B raw9351step0 raw9351step0Labels := by
      have ha : raw9351step0 = (fun i j => raw9351 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9351step0 raw9351; decide +kernel
      have hl : raw9351step0Labels = raw9351Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9351 raw9351Labels permutation184 permutation2
    _ = mixedMoment B node2746 node2746Labels := by rfl

def raw9352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw9352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9352 raw9352Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw9352 raw9352Labels = mixedMoment B raw9352step0 raw9352step0Labels := by
      have ha : raw9352step0 = (fun i j => raw9352 (permutation186 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9352step0 raw9352; decide +kernel
      have hl : raw9352step0Labels = raw9352Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9352 raw9352Labels permutation186 permutation2
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw9353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9353 raw9353Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw9353 raw9353Labels = mixedMoment B raw9353step0 raw9353step0Labels := by
      have ha : raw9353step0 = (fun i j => raw9353 (permutation599 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9353step0 raw9353; decide +kernel
      have hl : raw9353step0Labels = raw9353Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9353 raw9353Labels permutation599 permutation4
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw9354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9354 raw9354Labels = mixedMoment B node2573 node2573Labels := by
  calc
    mixedMoment B raw9354 raw9354Labels = mixedMoment B raw9354step0 raw9354step0Labels := by
      have ha : raw9354step0 = (fun i j => raw9354 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9354step0 raw9354; decide +kernel
      have hl : raw9354step0Labels = raw9354Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9354 raw9354Labels permutation158 permutation2
    _ = mixedMoment B node2573 node2573Labels := by rfl

def raw9355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9355 raw9355Labels = mixedMoment B node2573 node2573Labels := by
  calc
    _ = mixedMoment B node2573 node2573Labels := by rfl

def raw9356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw9356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9356 raw9356Labels = mixedMoment B node2564 node2564Labels := by
  calc
    mixedMoment B raw9356 raw9356Labels = mixedMoment B raw9356step0 raw9356step0Labels := by
      have ha : raw9356step0 = (fun i j => raw9356 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9356step0 raw9356; decide +kernel
      have hl : raw9356step0Labels = raw9356Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9356 raw9356Labels permutation153 permutation2
    _ = mixedMoment B node2564 node2564Labels := by rfl

def raw9357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9357 raw9357Labels = mixedMoment B node1421 node1421Labels := by
  calc
    mixedMoment B raw9357 raw9357Labels = mixedMoment B raw9357step0 raw9357step0Labels := by
      have ha : raw9357step0 = (fun i j => raw9357 (permutation665 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9357step0 raw9357; decide +kernel
      have hl : raw9357step0Labels = raw9357Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9357 raw9357Labels permutation665 permutation4
    _ = mixedMoment B node1421 node1421Labels := by rfl

def raw9358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9358 raw9358Labels = mixedMoment B node2641 node2641Labels := by
  calc
    mixedMoment B raw9358 raw9358Labels = mixedMoment B raw9358step0 raw9358step0Labels := by
      have hz : ∀ j, raw9358 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9358step0 = (fun i j => raw9358 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9358step0 raw9358; decide +kernel
      have hl : raw9358step0Labels = raw9358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9358 raw9358Labels permutation265 hz
    mixedMoment B raw9358step0 raw9358step0Labels = mixedMoment B raw9358step1 raw9358step1Labels := by
      have ha : raw9358step1 = (fun i j => raw9358step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9358step1 raw9358step0; decide +kernel
      have hl : raw9358step1Labels = raw9358step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9358step0 raw9358step0Labels permutation38 permutation2
    _ = mixedMoment B node2641 node2641Labels := by rfl

def raw9359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9359 raw9359Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw9359 raw9359Labels = mixedMoment B raw9359step0 raw9359step0Labels := by
      have hz : ∀ j, raw9359 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9359step0 = (fun i j => raw9359 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9359step0 raw9359; decide +kernel
      have hl : raw9359step0Labels = raw9359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9359 raw9359Labels permutation265 hz
    mixedMoment B raw9359step0 raw9359step0Labels = mixedMoment B raw9359step1 raw9359step1Labels := by
      have ha : raw9359step1 = (fun i j => raw9359step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9359step1 raw9359step0; decide +kernel
      have hl : raw9359step1Labels = raw9359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9359step0 raw9359step0Labels permutation40 permutation2
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw9360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9360step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9360 raw9360Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw9360 raw9360Labels = mixedMoment B raw9360step0 raw9360step0Labels := by
      have hz : ∀ j, raw9360 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9360step0 = (fun i j => raw9360 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9360step0 raw9360; decide +kernel
      have hl : raw9360step0Labels = raw9360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9360 raw9360Labels permutation265 hz
    mixedMoment B raw9360step0 raw9360step0Labels = mixedMoment B raw9360step1 raw9360step1Labels := by
      have ha : raw9360step1 = (fun i j => raw9360step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9360step1 raw9360step0; decide +kernel
      have hl : raw9360step1Labels = raw9360step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9360step0 raw9360step0Labels permutation42 permutation2
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw9361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9361step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9361step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9361 raw9361Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw9361 raw9361Labels = mixedMoment B raw9361step0 raw9361step0Labels := by
      have ha : raw9361step0 = (fun i j => raw9361 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9361step0 raw9361; decide +kernel
      have hl : raw9361step0Labels = raw9361Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9361 raw9361Labels permutation674 permutation7
    mixedMoment B raw9361step0 raw9361step0Labels = mixedMoment B raw9361step1 raw9361step1Labels := by
      have ha : raw9361step1 = raw9361step0 := by apply Matrix.ext; unfold raw9361step1 raw9361step0; decide +kernel
      have hl : raw9361step0Labels = labelEmbedding10 ∘ raw9361step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9361step0 raw9361step0Labels raw9361step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw9362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9362step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9362step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9362 raw9362Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw9362 raw9362Labels = mixedMoment B raw9362step0 raw9362step0Labels := by
      have hz : ∀ j, raw9362 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9362step0 = (fun i j => raw9362 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9362step0 raw9362; decide +kernel
      have hl : raw9362step0Labels = raw9362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9362 raw9362Labels permutation265 hz
    mixedMoment B raw9362step0 raw9362step0Labels = mixedMoment B raw9362step1 raw9362step1Labels := by
      have ha : raw9362step1 = (fun i j => raw9362step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9362step1 raw9362step0; decide +kernel
      have hl : raw9362step1Labels = raw9362step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9362step0 raw9362step0Labels permutation151 permutation7
    mixedMoment B raw9362step1 raw9362step1Labels = mixedMoment B raw9362step2 raw9362step2Labels := by
      have ha : raw9362step2 = raw9362step1 := by apply Matrix.ext; unfold raw9362step2 raw9362step1; decide +kernel
      have hl : raw9362step1Labels = labelEmbedding10 ∘ raw9362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9362step1 raw9362step1Labels raw9362step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw9363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9363step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9363step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9363 raw9363Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw9363 raw9363Labels = mixedMoment B raw9363step0 raw9363step0Labels := by
      have hz : ∀ j, raw9363 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9363step0 = (fun i j => raw9363 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9363step0 raw9363; decide +kernel
      have hl : raw9363step0Labels = raw9363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9363 raw9363Labels permutation265 hz
    mixedMoment B raw9363step0 raw9363step0Labels = mixedMoment B raw9363step1 raw9363step1Labels := by
      have ha : raw9363step1 = (fun i j => raw9363step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9363step1 raw9363step0; decide +kernel
      have hl : raw9363step1Labels = raw9363step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9363step0 raw9363step0Labels permutation149 permutation7
    mixedMoment B raw9363step1 raw9363step1Labels = mixedMoment B raw9363step2 raw9363step2Labels := by
      have ha : raw9363step2 = raw9363step1 := by apply Matrix.ext; unfold raw9363step2 raw9363step1; decide +kernel
      have hl : raw9363step1Labels = labelEmbedding10 ∘ raw9363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9363step1 raw9363step1Labels raw9363step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw9364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9364step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9364step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9364step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9364step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9364 raw9364Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw9364 raw9364Labels = mixedMoment B raw9364step0 raw9364step0Labels := by
      have hz : ∀ j, raw9364 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9364step0 = (fun i j => raw9364 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9364step0 raw9364; decide +kernel
      have hl : raw9364step0Labels = raw9364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9364 raw9364Labels permutation520 hz
    mixedMoment B raw9364step0 raw9364step0Labels = mixedMoment B raw9364step1 raw9364step1Labels := by
      have hz : ∀ j, raw9364step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9364step1 = (fun i j => raw9364step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9364step1 raw9364step0; decide +kernel
      have hl : raw9364step1Labels = raw9364step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9364step0 raw9364step0Labels permutation56 hz
    mixedMoment B raw9364step1 raw9364step1Labels = mixedMoment B raw9364step2 raw9364step2Labels := by
      have ha : raw9364step2 = (fun i j => raw9364step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9364step2 raw9364step1; decide +kernel
      have hl : raw9364step2Labels = raw9364step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9364step1 raw9364step1Labels permutation29 permutation7
    mixedMoment B raw9364step2 raw9364step2Labels = mixedMoment B raw9364step3 raw9364step3Labels := by
      have ha : raw9364step3 = raw9364step2 := by apply Matrix.ext; unfold raw9364step3 raw9364step2; decide +kernel
      have hl : raw9364step2Labels = labelEmbedding10 ∘ raw9364step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9364step2 raw9364step2Labels raw9364step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw9365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9365step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9365step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9365 raw9365Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw9365 raw9365Labels = mixedMoment B raw9365step0 raw9365step0Labels := by
      have hz : ∀ j, raw9365 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9365step0 = (fun i j => raw9365 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9365step0 raw9365; decide +kernel
      have hl : raw9365step0Labels = raw9365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9365 raw9365Labels permutation265 hz
    mixedMoment B raw9365step0 raw9365step0Labels = mixedMoment B raw9365step1 raw9365step1Labels := by
      have ha : raw9365step1 = (fun i j => raw9365step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9365step1 raw9365step0; decide +kernel
      have hl : raw9365step1Labels = raw9365step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9365step0 raw9365step0Labels permutation146 permutation6
    mixedMoment B raw9365step1 raw9365step1Labels = mixedMoment B raw9365step2 raw9365step2Labels := by
      have ha : raw9365step2 = raw9365step1 := by apply Matrix.ext; unfold raw9365step2 raw9365step1; decide +kernel
      have hl : raw9365step1Labels = labelEmbedding9 ∘ raw9365step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9365step1 raw9365step1Labels raw9365step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw9366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9366step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9366step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9366 raw9366Labels = mixedMoment B node4441 node4441Labels := by
  calc
    mixedMoment B raw9366 raw9366Labels = mixedMoment B raw9366step0 raw9366step0Labels := by
      have ha : raw9366step0 = (fun i j => raw9366 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9366step0 raw9366; decide +kernel
      have hl : raw9366step0Labels = raw9366Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9366 raw9366Labels permutation182 permutation3
    mixedMoment B raw9366step0 raw9366step0Labels = mixedMoment B raw9366step1 raw9366step1Labels := by
      have ha : raw9366step1 = raw9366step0 := by apply Matrix.ext; unfold raw9366step1 raw9366step0; decide +kernel
      have hl : raw9366step0Labels = labelEmbedding6 ∘ raw9366step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9366step0 raw9366step0Labels raw9366step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4441 node4441Labels := by rfl

def raw9367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9367step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9367step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9367 raw9367Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw9367 raw9367Labels = mixedMoment B raw9367step0 raw9367step0Labels := by
      have ha : raw9367step0 = (fun i j => raw9367 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9367step0 raw9367; decide +kernel
      have hl : raw9367step0Labels = raw9367Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9367 raw9367Labels permutation182 permutation3
    mixedMoment B raw9367step0 raw9367step0Labels = mixedMoment B raw9367step1 raw9367step1Labels := by
      have ha : raw9367step1 = raw9367step0 := by apply Matrix.ext; unfold raw9367step1 raw9367step0; decide +kernel
      have hl : raw9367step0Labels = labelEmbedding6 ∘ raw9367step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9367step0 raw9367step0Labels raw9367step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw9368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9368step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9368step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9368 raw9368Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw9368 raw9368Labels = mixedMoment B raw9368step0 raw9368step0Labels := by
      have ha : raw9368step0 = (fun i j => raw9368 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9368step0 raw9368; decide +kernel
      have hl : raw9368step0Labels = raw9368Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9368 raw9368Labels permutation206 permutation3
    mixedMoment B raw9368step0 raw9368step0Labels = mixedMoment B raw9368step1 raw9368step1Labels := by
      have ha : raw9368step1 = raw9368step0 := by apply Matrix.ext; unfold raw9368step1 raw9368step0; decide +kernel
      have hl : raw9368step0Labels = labelEmbedding6 ∘ raw9368step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9368step0 raw9368step0Labels raw9368step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw9369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9369step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9369step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9369step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9369 raw9369Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw9369 raw9369Labels = mixedMoment B raw9369step0 raw9369step0Labels := by
      have hz : ∀ j, raw9369 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9369step0 = (fun i j => raw9369 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9369step0 raw9369; decide +kernel
      have hl : raw9369step0Labels = raw9369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9369 raw9369Labels permutation520 hz
    mixedMoment B raw9369step0 raw9369step0Labels = mixedMoment B raw9369step1 raw9369step1Labels := by
      have ha : raw9369step1 = (fun i j => raw9369step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9369step1 raw9369step0; decide +kernel
      have hl : raw9369step1Labels = raw9369step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9369step0 raw9369step0Labels permutation137 permutation7
    mixedMoment B raw9369step1 raw9369step1Labels = mixedMoment B raw9369step2 raw9369step2Labels := by
      have ha : raw9369step2 = raw9369step1 := by apply Matrix.ext; unfold raw9369step2 raw9369step1; decide +kernel
      have hl : raw9369step1Labels = labelEmbedding10 ∘ raw9369step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9369step1 raw9369step1Labels raw9369step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw9370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw9370step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw9370step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9370 raw9370Labels = mixedMoment B node5278 node5278Labels := by
  calc
    mixedMoment B raw9370 raw9370Labels = mixedMoment B raw9370step0 raw9370step0Labels := by
      have ha : raw9370step0 = (fun i j => raw9370 (permutation186 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9370step0 raw9370; decide +kernel
      have hl : raw9370step0Labels = raw9370Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9370 raw9370Labels permutation186 permutation3
    mixedMoment B raw9370step0 raw9370step0Labels = mixedMoment B raw9370step1 raw9370step1Labels := by
      have ha : raw9370step1 = raw9370step0 := by apply Matrix.ext; unfold raw9370step1 raw9370step0; decide +kernel
      have hl : raw9370step0Labels = labelEmbedding6 ∘ raw9370step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9370step0 raw9370step0Labels raw9370step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5278 node5278Labels := by rfl

def raw9371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9371step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9371step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9371step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9371 raw9371Labels = mixedMoment B node4462 node4462Labels := by
  calc
    mixedMoment B raw9371 raw9371Labels = mixedMoment B raw9371step0 raw9371step0Labels := by
      have hz : ∀ j, raw9371 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9371step0 = (fun i j => raw9371 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9371step0 raw9371; decide +kernel
      have hl : raw9371step0Labels = raw9371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9371 raw9371Labels permutation265 hz
    mixedMoment B raw9371step0 raw9371step0Labels = mixedMoment B raw9371step1 raw9371step1Labels := by
      have ha : raw9371step1 = (fun i j => raw9371step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9371step1 raw9371step0; decide +kernel
      have hl : raw9371step1Labels = raw9371step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9371step0 raw9371step0Labels permutation40 permutation3
    mixedMoment B raw9371step1 raw9371step1Labels = mixedMoment B raw9371step2 raw9371step2Labels := by
      have ha : raw9371step2 = raw9371step1 := by apply Matrix.ext; unfold raw9371step2 raw9371step1; decide +kernel
      have hl : raw9371step1Labels = labelEmbedding6 ∘ raw9371step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9371step1 raw9371step1Labels raw9371step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4462 node4462Labels := by rfl

def raw9372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9372step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9372step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9372 raw9372Labels = mixedMoment B node5077 node5077Labels := by
  calc
    mixedMoment B raw9372 raw9372Labels = mixedMoment B raw9372step0 raw9372step0Labels := by
      have ha : raw9372step0 = (fun i j => raw9372 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9372step0 raw9372; decide +kernel
      have hl : raw9372step0Labels = raw9372Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9372 raw9372Labels permutation160 permutation3
    mixedMoment B raw9372step0 raw9372step0Labels = mixedMoment B raw9372step1 raw9372step1Labels := by
      have ha : raw9372step1 = raw9372step0 := by apply Matrix.ext; unfold raw9372step1 raw9372step0; decide +kernel
      have hl : raw9372step0Labels = labelEmbedding6 ∘ raw9372step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9372step0 raw9372step0Labels raw9372step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5077 node5077Labels := by rfl

def raw9373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9373step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9373step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9373step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9373 raw9373Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw9373 raw9373Labels = mixedMoment B raw9373step0 raw9373step0Labels := by
      have hz : ∀ j, raw9373 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9373step0 = (fun i j => raw9373 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9373step0 raw9373; decide +kernel
      have hl : raw9373step0Labels = raw9373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9373 raw9373Labels permutation265 hz
    mixedMoment B raw9373step0 raw9373step0Labels = mixedMoment B raw9373step1 raw9373step1Labels := by
      have ha : raw9373step1 = (fun i j => raw9373step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9373step1 raw9373step0; decide +kernel
      have hl : raw9373step1Labels = raw9373step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9373step0 raw9373step0Labels permutation40 permutation3
    mixedMoment B raw9373step1 raw9373step1Labels = mixedMoment B raw9373step2 raw9373step2Labels := by
      have ha : raw9373step2 = raw9373step1 := by apply Matrix.ext; unfold raw9373step2 raw9373step1; decide +kernel
      have hl : raw9373step1Labels = labelEmbedding6 ∘ raw9373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9373step1 raw9373step1Labels raw9373step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw9374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9374step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9374step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9374step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9374step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9374step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9374 raw9374Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw9374 raw9374Labels = mixedMoment B raw9374step0 raw9374step0Labels := by
      have hz : ∀ j, raw9374 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9374step0 = (fun i j => raw9374 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9374step0 raw9374; decide +kernel
      have hl : raw9374step0Labels = raw9374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9374 raw9374Labels permutation520 hz
    mixedMoment B raw9374step0 raw9374step0Labels = mixedMoment B raw9374step1 raw9374step1Labels := by
      have hz : ∀ j, raw9374step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9374step1 = (fun i j => raw9374step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9374step1 raw9374step0; decide +kernel
      have hl : raw9374step1Labels = raw9374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9374step0 raw9374step0Labels permutation56 hz
    mixedMoment B raw9374step1 raw9374step1Labels = mixedMoment B raw9374step2 raw9374step2Labels := by
      have ha : raw9374step2 = (fun i j => raw9374step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9374step2 raw9374step1; decide +kernel
      have hl : raw9374step2Labels = raw9374step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9374step1 raw9374step1Labels permutation10 permutation3
    mixedMoment B raw9374step2 raw9374step2Labels = mixedMoment B raw9374step3 raw9374step3Labels := by
      have ha : raw9374step3 = raw9374step2 := by apply Matrix.ext; unfold raw9374step3 raw9374step2; decide +kernel
      have hl : raw9374step2Labels = labelEmbedding6 ∘ raw9374step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9374step2 raw9374step2Labels raw9374step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw9375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw9375step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9375step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw9375step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9375 raw9375Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw9375 raw9375Labels = mixedMoment B raw9375step0 raw9375step0Labels := by
      have hz : ∀ j, raw9375 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9375step0 = (fun i j => raw9375 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9375step0 raw9375; decide +kernel
      have hl : raw9375step0Labels = raw9375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9375 raw9375Labels permutation265 hz
    mixedMoment B raw9375step0 raw9375step0Labels = mixedMoment B raw9375step1 raw9375step1Labels := by
      have ha : raw9375step1 = (fun i j => raw9375step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9375step1 raw9375step0; decide +kernel
      have hl : raw9375step1Labels = raw9375step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9375step0 raw9375step0Labels permutation43 permutation3
    mixedMoment B raw9375step1 raw9375step1Labels = mixedMoment B raw9375step2 raw9375step2Labels := by
      have ha : raw9375step2 = raw9375step1 := by apply Matrix.ext; unfold raw9375step2 raw9375step1; decide +kernel
      have hl : raw9375step1Labels = labelEmbedding6 ∘ raw9375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9375step1 raw9375step1Labels raw9375step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5288 node5288Labels := by rfl

def raw9376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9376step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9376step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9376 raw9376Labels = mixedMoment B node4462 node4462Labels := by
  calc
    mixedMoment B raw9376 raw9376Labels = mixedMoment B raw9376step0 raw9376step0Labels := by
      have hz : ∀ j, raw9376 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9376step0 = (fun i j => raw9376 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9376step0 raw9376; decide +kernel
      have hl : raw9376step0Labels = raw9376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9376 raw9376Labels permutation265 hz
    mixedMoment B raw9376step0 raw9376step0Labels = mixedMoment B raw9376step1 raw9376step1Labels := by
      have ha : raw9376step1 = (fun i j => raw9376step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9376step1 raw9376step0; decide +kernel
      have hl : raw9376step1Labels = raw9376step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9376step0 raw9376step0Labels permutation34 permutation3
    mixedMoment B raw9376step1 raw9376step1Labels = mixedMoment B raw9376step2 raw9376step2Labels := by
      have ha : raw9376step2 = raw9376step1 := by apply Matrix.ext; unfold raw9376step2 raw9376step1; decide +kernel
      have hl : raw9376step1Labels = labelEmbedding6 ∘ raw9376step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9376step1 raw9376step1Labels raw9376step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4462 node4462Labels := by rfl

def raw9377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9377step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9377 raw9377Labels = mixedMoment B node5077 node5077Labels := by
  calc
    mixedMoment B raw9377 raw9377Labels = mixedMoment B raw9377step0 raw9377step0Labels := by
      have ha : raw9377step0 = (fun i j => raw9377 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9377step0 raw9377; decide +kernel
      have hl : raw9377step0Labels = raw9377Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9377 raw9377Labels permutation154 permutation3
    mixedMoment B raw9377step0 raw9377step0Labels = mixedMoment B raw9377step1 raw9377step1Labels := by
      have ha : raw9377step1 = raw9377step0 := by apply Matrix.ext; unfold raw9377step1 raw9377step0; decide +kernel
      have hl : raw9377step0Labels = labelEmbedding6 ∘ raw9377step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9377step0 raw9377step0Labels raw9377step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5077 node5077Labels := by rfl

def raw9378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9378step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9378step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9378 raw9378Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw9378 raw9378Labels = mixedMoment B raw9378step0 raw9378step0Labels := by
      have hz : ∀ j, raw9378 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9378step0 = (fun i j => raw9378 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9378step0 raw9378; decide +kernel
      have hl : raw9378step0Labels = raw9378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9378 raw9378Labels permutation265 hz
    mixedMoment B raw9378step0 raw9378step0Labels = mixedMoment B raw9378step1 raw9378step1Labels := by
      have ha : raw9378step1 = (fun i j => raw9378step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9378step1 raw9378step0; decide +kernel
      have hl : raw9378step1Labels = raw9378step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9378step0 raw9378step0Labels permutation34 permutation3
    mixedMoment B raw9378step1 raw9378step1Labels = mixedMoment B raw9378step2 raw9378step2Labels := by
      have ha : raw9378step2 = raw9378step1 := by apply Matrix.ext; unfold raw9378step2 raw9378step1; decide +kernel
      have hl : raw9378step1Labels = labelEmbedding6 ∘ raw9378step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9378step1 raw9378step1Labels raw9378step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw9379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9379step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9379step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9379step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9379 raw9379Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw9379 raw9379Labels = mixedMoment B raw9379step0 raw9379step0Labels := by
      have hz : ∀ j, raw9379 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9379step0 = (fun i j => raw9379 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9379step0 raw9379; decide +kernel
      have hl : raw9379step0Labels = raw9379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9379 raw9379Labels permutation520 hz
    mixedMoment B raw9379step0 raw9379step0Labels = mixedMoment B raw9379step1 raw9379step1Labels := by
      have hz : ∀ j, raw9379step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9379step1 = (fun i j => raw9379step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9379step1 raw9379step0; decide +kernel
      have hl : raw9379step1Labels = raw9379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9379step0 raw9379step0Labels permutation56 hz
    mixedMoment B raw9379step1 raw9379step1Labels = mixedMoment B raw9379step2 raw9379step2Labels := by
      have ha : raw9379step2 = (fun i j => raw9379step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9379step2 raw9379step1; decide +kernel
      have hl : raw9379step2Labels = raw9379step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9379step1 raw9379step1Labels permutation8 permutation3
    mixedMoment B raw9379step2 raw9379step2Labels = mixedMoment B raw9379step3 raw9379step3Labels := by
      have ha : raw9379step3 = raw9379step2 := by apply Matrix.ext; unfold raw9379step3 raw9379step2; decide +kernel
      have hl : raw9379step2Labels = labelEmbedding6 ∘ raw9379step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9379step2 raw9379step2Labels raw9379step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw9380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw9380step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw9380step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9380 raw9380Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw9380 raw9380Labels = mixedMoment B raw9380step0 raw9380step0Labels := by
      have hz : ∀ j, raw9380 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9380step0 = (fun i j => raw9380 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9380step0 raw9380; decide +kernel
      have hl : raw9380step0Labels = raw9380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9380 raw9380Labels permutation265 hz
    mixedMoment B raw9380step0 raw9380step0Labels = mixedMoment B raw9380step1 raw9380step1Labels := by
      have ha : raw9380step1 = (fun i j => raw9380step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9380step1 raw9380step0; decide +kernel
      have hl : raw9380step1Labels = raw9380step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9380step0 raw9380step0Labels permutation37 permutation3
    mixedMoment B raw9380step1 raw9380step1Labels = mixedMoment B raw9380step2 raw9380step2Labels := by
      have ha : raw9380step2 = raw9380step1 := by apply Matrix.ext; unfold raw9380step2 raw9380step1; decide +kernel
      have hl : raw9380step1Labels = labelEmbedding6 ∘ raw9380step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9380step1 raw9380step1Labels raw9380step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5288 node5288Labels := by rfl

def raw9381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9381step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9381step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9381 raw9381Labels = mixedMoment B node4443 node4443Labels := by
  calc
    mixedMoment B raw9381 raw9381Labels = mixedMoment B raw9381step0 raw9381step0Labels := by
      have hz : ∀ j, raw9381 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9381step0 = (fun i j => raw9381 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9381step0 raw9381; decide +kernel
      have hl : raw9381step0Labels = raw9381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9381 raw9381Labels permutation265 hz
    mixedMoment B raw9381step0 raw9381step0Labels = mixedMoment B raw9381step1 raw9381step1Labels := by
      have ha : raw9381step1 = (fun i j => raw9381step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9381step1 raw9381step0; decide +kernel
      have hl : raw9381step1Labels = raw9381step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9381step0 raw9381step0Labels permutation33 permutation3
    mixedMoment B raw9381step1 raw9381step1Labels = mixedMoment B raw9381step2 raw9381step2Labels := by
      have ha : raw9381step2 = raw9381step1 := by apply Matrix.ext; unfold raw9381step2 raw9381step1; decide +kernel
      have hl : raw9381step1Labels = labelEmbedding6 ∘ raw9381step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9381step1 raw9381step1Labels raw9381step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4443 node4443Labels := by rfl

def raw9382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9382step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9382step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9382 raw9382Labels = mixedMoment B node5066 node5066Labels := by
  calc
    mixedMoment B raw9382 raw9382Labels = mixedMoment B raw9382step0 raw9382step0Labels := by
      have ha : raw9382step0 = (fun i j => raw9382 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9382step0 raw9382; decide +kernel
      have hl : raw9382step0Labels = raw9382Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9382 raw9382Labels permutation153 permutation3
    mixedMoment B raw9382step0 raw9382step0Labels = mixedMoment B raw9382step1 raw9382step1Labels := by
      have ha : raw9382step1 = raw9382step0 := by apply Matrix.ext; unfold raw9382step1 raw9382step0; decide +kernel
      have hl : raw9382step0Labels = labelEmbedding6 ∘ raw9382step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9382step0 raw9382step0Labels raw9382step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5066 node5066Labels := by rfl

def raw9383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9383step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9383step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9383step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9383 raw9383Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw9383 raw9383Labels = mixedMoment B raw9383step0 raw9383step0Labels := by
      have hz : ∀ j, raw9383 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9383step0 = (fun i j => raw9383 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9383step0 raw9383; decide +kernel
      have hl : raw9383step0Labels = raw9383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9383 raw9383Labels permutation265 hz
    mixedMoment B raw9383step0 raw9383step0Labels = mixedMoment B raw9383step1 raw9383step1Labels := by
      have ha : raw9383step1 = (fun i j => raw9383step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9383step1 raw9383step0; decide +kernel
      have hl : raw9383step1Labels = raw9383step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9383step0 raw9383step0Labels permutation33 permutation3
    mixedMoment B raw9383step1 raw9383step1Labels = mixedMoment B raw9383step2 raw9383step2Labels := by
      have ha : raw9383step2 = raw9383step1 := by apply Matrix.ext; unfold raw9383step2 raw9383step1; decide +kernel
      have hl : raw9383step1Labels = labelEmbedding6 ∘ raw9383step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9383step1 raw9383step1Labels raw9383step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw9384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9384step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9384 raw9384Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw9384 raw9384Labels = mixedMoment B raw9384step0 raw9384step0Labels := by
      have hz : ∀ j, raw9384 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9384step0 = (fun i j => raw9384 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9384step0 raw9384; decide +kernel
      have hl : raw9384step0Labels = raw9384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9384 raw9384Labels permutation265 hz
    mixedMoment B raw9384step0 raw9384step0Labels = mixedMoment B raw9384step1 raw9384step1Labels := by
      have ha : raw9384step1 = (fun i j => raw9384step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9384step1 raw9384step0; decide +kernel
      have hl : raw9384step1Labels = raw9384step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9384step0 raw9384step0Labels permutation39 permutation3
    mixedMoment B raw9384step1 raw9384step1Labels = mixedMoment B raw9384step2 raw9384step2Labels := by
      have ha : raw9384step2 = raw9384step1 := by apply Matrix.ext; unfold raw9384step2 raw9384step1; decide +kernel
      have hl : raw9384step1Labels = labelEmbedding6 ∘ raw9384step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9384step1 raw9384step1Labels raw9384step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw9385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9385step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9385step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9385 raw9385Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw9385 raw9385Labels = mixedMoment B raw9385step0 raw9385step0Labels := by
      have hz : ∀ j, raw9385 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9385step0 = (fun i j => raw9385 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9385step0 raw9385; decide +kernel
      have hl : raw9385step0Labels = raw9385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9385 raw9385Labels permutation265 hz
    mixedMoment B raw9385step0 raw9385step0Labels = mixedMoment B raw9385step1 raw9385step1Labels := by
      have ha : raw9385step1 = (fun i j => raw9385step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9385step1 raw9385step0; decide +kernel
      have hl : raw9385step1Labels = raw9385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9385step0 raw9385step0Labels permutation33 permutation3
    mixedMoment B raw9385step1 raw9385step1Labels = mixedMoment B raw9385step2 raw9385step2Labels := by
      have ha : raw9385step2 = raw9385step1 := by apply Matrix.ext; unfold raw9385step2 raw9385step1; decide +kernel
      have hl : raw9385step1Labels = labelEmbedding6 ∘ raw9385step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9385step1 raw9385step1Labels raw9385step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

def raw9386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw9386step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw9386step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9386 raw9386Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw9386 raw9386Labels = mixedMoment B raw9386step0 raw9386step0Labels := by
      have hz : ∀ j, raw9386 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9386step0 = (fun i j => raw9386 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9386step0 raw9386; decide +kernel
      have hl : raw9386step0Labels = raw9386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9386 raw9386Labels permutation265 hz
    mixedMoment B raw9386step0 raw9386step0Labels = mixedMoment B raw9386step1 raw9386step1Labels := by
      have ha : raw9386step1 = (fun i j => raw9386step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9386step1 raw9386step0; decide +kernel
      have hl : raw9386step1Labels = raw9386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9386step0 raw9386step0Labels permutation32 permutation3
    mixedMoment B raw9386step1 raw9386step1Labels = mixedMoment B raw9386step2 raw9386step2Labels := by
      have ha : raw9386step2 = raw9386step1 := by apply Matrix.ext; unfold raw9386step2 raw9386step1; decide +kernel
      have hl : raw9386step1Labels = labelEmbedding6 ∘ raw9386step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9386step1 raw9386step1Labels raw9386step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw9387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw9387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9387 raw9387Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw9387 raw9387Labels = mixedMoment B raw9387step0 raw9387step0Labels := by
      have ha : raw9387step0 = (fun i j => raw9387 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9387step0 raw9387; decide +kernel
      have hl : raw9387step0Labels = raw9387Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9387 raw9387Labels permutation682 permutation2
    mixedMoment B raw9387step0 raw9387step0Labels = mixedMoment B raw9387step1 raw9387step1Labels := by
      have ha : raw9387step1 = -raw9387step0 := by apply Matrix.ext; change ∀ i j, raw9387step1 i j = -(raw9387step0 i j); unfold raw9387step1 raw9387step0; decide +kernel
      have hl : raw9387step1Labels = raw9387step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw9388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9388step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9388 raw9388Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw9388 raw9388Labels = mixedMoment B raw9388step0 raw9388step0Labels := by
      have hz : ∀ j, raw9388 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9388step0 = (fun i j => raw9388 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9388step0 raw9388; decide +kernel
      have hl : raw9388step0Labels = raw9388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9388 raw9388Labels permutation265 hz
    mixedMoment B raw9388step0 raw9388step0Labels = mixedMoment B raw9388step1 raw9388step1Labels := by
      have ha : raw9388step1 = (fun i j => raw9388step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9388step1 raw9388step0; decide +kernel
      have hl : raw9388step1Labels = raw9388step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9388step0 raw9388step0Labels permutation151 permutation2
    mixedMoment B raw9388step1 raw9388step1Labels = mixedMoment B raw9388step2 raw9388step2Labels := by
      have ha : raw9388step2 = -raw9388step1 := by apply Matrix.ext; change ∀ i j, raw9388step2 i j = -(raw9388step1 i j); unfold raw9388step2 raw9388step1; decide +kernel
      have hl : raw9388step2Labels = raw9388step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw9389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9389 raw9389Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw9389 raw9389Labels = mixedMoment B raw9389step0 raw9389step0Labels := by
      have hz : ∀ j, raw9389 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9389step0 = (fun i j => raw9389 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9389step0 raw9389; decide +kernel
      have hl : raw9389step0Labels = raw9389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9389 raw9389Labels permutation265 hz
    mixedMoment B raw9389step0 raw9389step0Labels = mixedMoment B raw9389step1 raw9389step1Labels := by
      have ha : raw9389step1 = (fun i j => raw9389step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9389step1 raw9389step0; decide +kernel
      have hl : raw9389step1Labels = raw9389step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9389step0 raw9389step0Labels permutation149 permutation2
    mixedMoment B raw9389step1 raw9389step1Labels = mixedMoment B raw9389step2 raw9389step2Labels := by
      have ha : raw9389step2 = -raw9389step1 := by apply Matrix.ext; change ∀ i j, raw9389step2 i j = -(raw9389step1 i j); unfold raw9389step2 raw9389step1; decide +kernel
      have hl : raw9389step2Labels = raw9389step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw9390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw9390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw9390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw9390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9390step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9390step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9390step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9390 raw9390Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw9390 raw9390Labels = mixedMoment B raw9390step0 raw9390step0Labels := by
      have hz : ∀ j, raw9390 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9390step0 = (fun i j => raw9390 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9390step0 raw9390; decide +kernel
      have hl : raw9390step0Labels = raw9390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9390 raw9390Labels permutation520 hz
    mixedMoment B raw9390step0 raw9390step0Labels = mixedMoment B raw9390step1 raw9390step1Labels := by
      have hz : ∀ j, raw9390step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9390step1 = (fun i j => raw9390step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9390step1 raw9390step0; decide +kernel
      have hl : raw9390step1Labels = raw9390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9390step0 raw9390step0Labels permutation56 hz
    mixedMoment B raw9390step1 raw9390step1Labels = mixedMoment B raw9390step2 raw9390step2Labels := by
      have ha : raw9390step2 = (fun i j => raw9390step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9390step2 raw9390step1; decide +kernel
      have hl : raw9390step2Labels = raw9390step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9390step1 raw9390step1Labels permutation29 permutation2
    mixedMoment B raw9390step2 raw9390step2Labels = mixedMoment B raw9390step3 raw9390step3Labels := by
      have ha : raw9390step3 = -raw9390step2 := by apply Matrix.ext; change ∀ i j, raw9390step3 i j = -(raw9390step2 i j); unfold raw9390step3 raw9390step2; decide +kernel
      have hl : raw9390step3Labels = raw9390step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw9391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9391 raw9391Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw9391 raw9391Labels = mixedMoment B raw9391step0 raw9391step0Labels := by
      have ha : raw9391step0 = (fun i j => raw9391 (permutation617 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9391step0 raw9391; decide +kernel
      have hl : raw9391step0Labels = raw9391Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9391 raw9391Labels permutation617 permutation6
    _ = mixedMoment B node3085 node3085Labels := by rfl

def raw9392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw9392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9392 raw9392Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw9392 raw9392Labels = mixedMoment B raw9392step0 raw9392step0Labels := by
      have hz : ∀ j, raw9392 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9392step0 = (fun i j => raw9392 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9392step0 raw9392; decide +kernel
      have hl : raw9392step0Labels = raw9392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9392 raw9392Labels permutation265 hz
    mixedMoment B raw9392step0 raw9392step0Labels = mixedMoment B raw9392step1 raw9392step1Labels := by
      have ha : raw9392step1 = (fun i j => raw9392step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9392step1 raw9392step0; decide +kernel
      have hl : raw9392step1Labels = raw9392step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9392step0 raw9392step0Labels permutation146 permutation6
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw9393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw9393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9393 raw9393Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw9393 raw9393Labels = mixedMoment B raw9393step0 raw9393step0Labels := by
      have hz : ∀ j, raw9393 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9393step0 = (fun i j => raw9393 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9393step0 raw9393; decide +kernel
      have hl : raw9393step0Labels = raw9393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9393 raw9393Labels permutation265 hz
    mixedMoment B raw9393step0 raw9393step0Labels = mixedMoment B raw9393step1 raw9393step1Labels := by
      have ha : raw9393step1 = (fun i j => raw9393step0 (permutation147 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9393step1 raw9393step0; decide +kernel
      have hl : raw9393step1Labels = raw9393step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9393step0 raw9393step0Labels permutation147 permutation6
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw9394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9394step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9394step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9394 raw9394Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw9394 raw9394Labels = mixedMoment B raw9394step0 raw9394step0Labels := by
      have hz : ∀ j, raw9394 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9394step0 = (fun i j => raw9394 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9394step0 raw9394; decide +kernel
      have hl : raw9394step0Labels = raw9394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9394 raw9394Labels permutation520 hz
    mixedMoment B raw9394step0 raw9394step0Labels = mixedMoment B raw9394step1 raw9394step1Labels := by
      have hz : ∀ j, raw9394step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9394step1 = (fun i j => raw9394step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9394step1 raw9394step0; decide +kernel
      have hl : raw9394step1Labels = raw9394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9394step0 raw9394step0Labels permutation56 hz
    mixedMoment B raw9394step1 raw9394step1Labels = mixedMoment B raw9394step2 raw9394step2Labels := by
      have ha : raw9394step2 = (fun i j => raw9394step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9394step2 raw9394step1; decide +kernel
      have hl : raw9394step2Labels = raw9394step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9394step1 raw9394step1Labels permutation26 permutation6
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw9395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9395 raw9395Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw9395 raw9395Labels = mixedMoment B raw9395step0 raw9395step0Labels := by
      have hz : ∀ j, raw9395 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9395step0 = (fun i j => raw9395 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9395step0 raw9395; decide +kernel
      have hl : raw9395step0Labels = raw9395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9395 raw9395Labels permutation265 hz
    mixedMoment B raw9395step0 raw9395step0Labels = mixedMoment B raw9395step1 raw9395step1Labels := by
      have ha : raw9395step1 = (fun i j => raw9395step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9395step1 raw9395step0; decide +kernel
      have hl : raw9395step1Labels = raw9395step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9395step0 raw9395step0Labels permutation146 permutation6
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw9396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9396 raw9396Labels = mixedMoment B node1023 node1023Labels := by
  calc
    mixedMoment B raw9396 raw9396Labels = mixedMoment B raw9396step0 raw9396step0Labels := by
      have ha : raw9396step0 = (fun i j => raw9396 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9396step0 raw9396; decide +kernel
      have hl : raw9396step0Labels = raw9396Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9396 raw9396Labels permutation182 permutation3
    _ = mixedMoment B node1023 node1023Labels := by rfl

def raw9397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9397 raw9397Labels = mixedMoment B node2573 node2573Labels := by
  calc
    mixedMoment B raw9397 raw9397Labels = mixedMoment B raw9397step0 raw9397step0Labels := by
      have ha : raw9397step0 = (fun i j => raw9397 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9397step0 raw9397; decide +kernel
      have hl : raw9397step0Labels = raw9397Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9397 raw9397Labels permutation182 permutation3
    _ = mixedMoment B node2573 node2573Labels := by rfl

def raw9398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9398 raw9398Labels = mixedMoment B node2573 node2573Labels := by
  calc
    mixedMoment B raw9398 raw9398Labels = mixedMoment B raw9398step0 raw9398step0Labels := by
      have ha : raw9398step0 = (fun i j => raw9398 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9398step0 raw9398; decide +kernel
      have hl : raw9398step0Labels = raw9398Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9398 raw9398Labels permutation206 permutation3
    _ = mixedMoment B node2573 node2573Labels := by rfl

def raw9399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9399 raw9399Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw9399 raw9399Labels = mixedMoment B raw9399step0 raw9399step0Labels := by
      have hz : ∀ j, raw9399 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9399step0 = (fun i j => raw9399 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9399step0 raw9399; decide +kernel
      have hl : raw9399step0Labels = raw9399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9399 raw9399Labels permutation520 hz
    mixedMoment B raw9399step0 raw9399step0Labels = mixedMoment B raw9399step1 raw9399step1Labels := by
      have ha : raw9399step1 = (fun i j => raw9399step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9399step1 raw9399step0; decide +kernel
      have hl : raw9399step1Labels = raw9399step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9399step0 raw9399step0Labels permutation40 permutation3
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw9400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw9400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9400 raw9400Labels = mixedMoment B node2747 node2747Labels := by
  calc
    mixedMoment B raw9400 raw9400Labels = mixedMoment B raw9400step0 raw9400step0Labels := by
      have ha : raw9400step0 = (fun i j => raw9400 (permutation186 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9400step0 raw9400; decide +kernel
      have hl : raw9400step0Labels = raw9400Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9400 raw9400Labels permutation186 permutation3
    _ = mixedMoment B node2747 node2747Labels := by rfl

def raw9401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9401 raw9401Labels = mixedMoment B node1045 node1045Labels := by
  calc
    mixedMoment B raw9401 raw9401Labels = mixedMoment B raw9401step0 raw9401step0Labels := by
      have hz : ∀ j, raw9401 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9401step0 = (fun i j => raw9401 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9401step0 raw9401; decide +kernel
      have hl : raw9401step0Labels = raw9401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9401 raw9401Labels permutation265 hz
    mixedMoment B raw9401step0 raw9401step0Labels = mixedMoment B raw9401step1 raw9401step1Labels := by
      have ha : raw9401step1 = (fun i j => raw9401step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9401step1 raw9401step0; decide +kernel
      have hl : raw9401step1Labels = raw9401step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9401step0 raw9401step0Labels permutation40 permutation3
    _ = mixedMoment B node1045 node1045Labels := by rfl

def raw9402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9402 raw9402Labels = mixedMoment B node2484 node2484Labels := by
  calc
    mixedMoment B raw9402 raw9402Labels = mixedMoment B raw9402step0 raw9402step0Labels := by
      have ha : raw9402step0 = (fun i j => raw9402 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9402step0 raw9402; decide +kernel
      have hl : raw9402step0Labels = raw9402Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9402 raw9402Labels permutation160 permutation3
    _ = mixedMoment B node2484 node2484Labels := by rfl

def raw9403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9403 raw9403Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw9403 raw9403Labels = mixedMoment B raw9403step0 raw9403step0Labels := by
      have hz : ∀ j, raw9403 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9403step0 = (fun i j => raw9403 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9403step0 raw9403; decide +kernel
      have hl : raw9403step0Labels = raw9403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9403 raw9403Labels permutation265 hz
    mixedMoment B raw9403step0 raw9403step0Labels = mixedMoment B raw9403step1 raw9403step1Labels := by
      have ha : raw9403step1 = (fun i j => raw9403step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9403step1 raw9403step0; decide +kernel
      have hl : raw9403step1Labels = raw9403step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9403step0 raw9403step0Labels permutation40 permutation3
    _ = mixedMoment B node2600 node2600Labels := by rfl

def raw9404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9404step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9404 raw9404Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw9404 raw9404Labels = mixedMoment B raw9404step0 raw9404step0Labels := by
      have hz : ∀ j, raw9404 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9404step0 = (fun i j => raw9404 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9404step0 raw9404; decide +kernel
      have hl : raw9404step0Labels = raw9404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9404 raw9404Labels permutation520 hz
    mixedMoment B raw9404step0 raw9404step0Labels = mixedMoment B raw9404step1 raw9404step1Labels := by
      have hz : ∀ j, raw9404step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9404step1 = (fun i j => raw9404step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9404step1 raw9404step0; decide +kernel
      have hl : raw9404step1Labels = raw9404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9404step0 raw9404step0Labels permutation56 hz
    mixedMoment B raw9404step1 raw9404step1Labels = mixedMoment B raw9404step2 raw9404step2Labels := by
      have ha : raw9404step2 = (fun i j => raw9404step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9404step2 raw9404step1; decide +kernel
      have hl : raw9404step2Labels = raw9404step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9404step1 raw9404step1Labels permutation10 permutation3
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw9405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9405step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw9405step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9405 raw9405Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw9405 raw9405Labels = mixedMoment B raw9405step0 raw9405step0Labels := by
      have hz : ∀ j, raw9405 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9405step0 = (fun i j => raw9405 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9405step0 raw9405; decide +kernel
      have hl : raw9405step0Labels = raw9405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9405 raw9405Labels permutation265 hz
    mixedMoment B raw9405step0 raw9405step0Labels = mixedMoment B raw9405step1 raw9405step1Labels := by
      have ha : raw9405step1 = (fun i j => raw9405step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9405step1 raw9405step0; decide +kernel
      have hl : raw9405step1Labels = raw9405step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9405step0 raw9405step0Labels permutation43 permutation3
    _ = mixedMoment B node2760 node2760Labels := by rfl

def raw9406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9406 raw9406Labels = mixedMoment B node1045 node1045Labels := by
  calc
    mixedMoment B raw9406 raw9406Labels = mixedMoment B raw9406step0 raw9406step0Labels := by
      have hz : ∀ j, raw9406 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9406step0 = (fun i j => raw9406 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9406step0 raw9406; decide +kernel
      have hl : raw9406step0Labels = raw9406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9406 raw9406Labels permutation265 hz
    mixedMoment B raw9406step0 raw9406step0Labels = mixedMoment B raw9406step1 raw9406step1Labels := by
      have ha : raw9406step1 = (fun i j => raw9406step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9406step1 raw9406step0; decide +kernel
      have hl : raw9406step1Labels = raw9406step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9406step0 raw9406step0Labels permutation34 permutation3
    _ = mixedMoment B node1045 node1045Labels := by rfl

def raw9407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9407 raw9407Labels = mixedMoment B node2484 node2484Labels := by
  calc
    mixedMoment B raw9407 raw9407Labels = mixedMoment B raw9407step0 raw9407step0Labels := by
      have ha : raw9407step0 = (fun i j => raw9407 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9407step0 raw9407; decide +kernel
      have hl : raw9407step0Labels = raw9407Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9407 raw9407Labels permutation154 permutation3
    _ = mixedMoment B node2484 node2484Labels := by rfl

def raw9408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9408 raw9408Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw9408 raw9408Labels = mixedMoment B raw9408step0 raw9408step0Labels := by
      have hz : ∀ j, raw9408 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9408step0 = (fun i j => raw9408 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9408step0 raw9408; decide +kernel
      have hl : raw9408step0Labels = raw9408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9408 raw9408Labels permutation265 hz
    mixedMoment B raw9408step0 raw9408step0Labels = mixedMoment B raw9408step1 raw9408step1Labels := by
      have ha : raw9408step1 = (fun i j => raw9408step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9408step1 raw9408step0; decide +kernel
      have hl : raw9408step1Labels = raw9408step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9408step0 raw9408step0Labels permutation34 permutation3
    _ = mixedMoment B node2600 node2600Labels := by rfl

def raw9409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9409step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9409step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw9409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9409 raw9409Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw9409 raw9409Labels = mixedMoment B raw9409step0 raw9409step0Labels := by
      have hz : ∀ j, raw9409 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9409step0 = (fun i j => raw9409 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9409step0 raw9409; decide +kernel
      have hl : raw9409step0Labels = raw9409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9409 raw9409Labels permutation520 hz
    mixedMoment B raw9409step0 raw9409step0Labels = mixedMoment B raw9409step1 raw9409step1Labels := by
      have hz : ∀ j, raw9409step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9409step1 = (fun i j => raw9409step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9409step1 raw9409step0; decide +kernel
      have hl : raw9409step1Labels = raw9409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9409step0 raw9409step0Labels permutation56 hz
    mixedMoment B raw9409step1 raw9409step1Labels = mixedMoment B raw9409step2 raw9409step2Labels := by
      have ha : raw9409step2 = (fun i j => raw9409step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9409step2 raw9409step1; decide +kernel
      have hl : raw9409step2Labels = raw9409step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9409step1 raw9409step1Labels permutation8 permutation3
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw9410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw9410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9410 raw9410Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw9410 raw9410Labels = mixedMoment B raw9410step0 raw9410step0Labels := by
      have hz : ∀ j, raw9410 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9410step0 = (fun i j => raw9410 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9410step0 raw9410; decide +kernel
      have hl : raw9410step0Labels = raw9410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9410 raw9410Labels permutation265 hz
    mixedMoment B raw9410step0 raw9410step0Labels = mixedMoment B raw9410step1 raw9410step1Labels := by
      have ha : raw9410step1 = (fun i j => raw9410step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9410step1 raw9410step0; decide +kernel
      have hl : raw9410step1Labels = raw9410step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9410step0 raw9410step0Labels permutation37 permutation3
    _ = mixedMoment B node2760 node2760Labels := by rfl

def raw9411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9411 raw9411Labels = mixedMoment B node1025 node1025Labels := by
  calc
    mixedMoment B raw9411 raw9411Labels = mixedMoment B raw9411step0 raw9411step0Labels := by
      have hz : ∀ j, raw9411 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9411step0 = (fun i j => raw9411 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9411step0 raw9411; decide +kernel
      have hl : raw9411step0Labels = raw9411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9411 raw9411Labels permutation265 hz
    mixedMoment B raw9411step0 raw9411step0Labels = mixedMoment B raw9411step1 raw9411step1Labels := by
      have ha : raw9411step1 = (fun i j => raw9411step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9411step1 raw9411step0; decide +kernel
      have hl : raw9411step1Labels = raw9411step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9411step0 raw9411step0Labels permutation33 permutation3
    _ = mixedMoment B node1025 node1025Labels := by rfl

def raw9412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9412 raw9412Labels = mixedMoment B node2472 node2472Labels := by
  calc
    mixedMoment B raw9412 raw9412Labels = mixedMoment B raw9412step0 raw9412step0Labels := by
      have ha : raw9412step0 = (fun i j => raw9412 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9412step0 raw9412; decide +kernel
      have hl : raw9412step0Labels = raw9412Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9412 raw9412Labels permutation153 permutation3
    _ = mixedMoment B node2472 node2472Labels := by rfl

def raw9413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9413 raw9413Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw9413 raw9413Labels = mixedMoment B raw9413step0 raw9413step0Labels := by
      have hz : ∀ j, raw9413 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9413step0 = (fun i j => raw9413 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9413step0 raw9413; decide +kernel
      have hl : raw9413step0Labels = raw9413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9413 raw9413Labels permutation265 hz
    mixedMoment B raw9413step0 raw9413step0Labels = mixedMoment B raw9413step1 raw9413step1Labels := by
      have ha : raw9413step1 = (fun i j => raw9413step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9413step1 raw9413step0; decide +kernel
      have hl : raw9413step1Labels = raw9413step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9413step0 raw9413step0Labels permutation33 permutation3
    _ = mixedMoment B node2575 node2575Labels := by rfl

def raw9414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9414step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw9414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9414 raw9414Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw9414 raw9414Labels = mixedMoment B raw9414step0 raw9414step0Labels := by
      have hz : ∀ j, raw9414 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9414step0 = (fun i j => raw9414 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9414step0 raw9414; decide +kernel
      have hl : raw9414step0Labels = raw9414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9414 raw9414Labels permutation265 hz
    mixedMoment B raw9414step0 raw9414step0Labels = mixedMoment B raw9414step1 raw9414step1Labels := by
      have ha : raw9414step1 = (fun i j => raw9414step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9414step1 raw9414step0; decide +kernel
      have hl : raw9414step1Labels = raw9414step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9414step0 raw9414step0Labels permutation39 permutation3
    _ = mixedMoment B node2575 node2575Labels := by rfl

def raw9415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw9415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9415 raw9415Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw9415 raw9415Labels = mixedMoment B raw9415step0 raw9415step0Labels := by
      have hz : ∀ j, raw9415 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9415step0 = (fun i j => raw9415 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9415step0 raw9415; decide +kernel
      have hl : raw9415step0Labels = raw9415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9415 raw9415Labels permutation265 hz
    mixedMoment B raw9415step0 raw9415step0Labels = mixedMoment B raw9415step1 raw9415step1Labels := by
      have ha : raw9415step1 = (fun i j => raw9415step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9415step1 raw9415step0; decide +kernel
      have hl : raw9415step1Labels = raw9415step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9415step0 raw9415step0Labels permutation33 permutation3
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw9416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9416step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw9416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9416 raw9416Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw9416 raw9416Labels = mixedMoment B raw9416step0 raw9416step0Labels := by
      have hz : ∀ j, raw9416 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9416step0 = (fun i j => raw9416 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9416step0 raw9416; decide +kernel
      have hl : raw9416step0Labels = raw9416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9416 raw9416Labels permutation265 hz
    mixedMoment B raw9416step0 raw9416step0Labels = mixedMoment B raw9416step1 raw9416step1Labels := by
      have ha : raw9416step1 = (fun i j => raw9416step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9416step1 raw9416step0; decide +kernel
      have hl : raw9416step1Labels = raw9416step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9416step0 raw9416step0Labels permutation32 permutation3
    _ = mixedMoment B node1024 node1024Labels := by rfl

def raw9417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw9417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9417 raw9417Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw9417 raw9417Labels = mixedMoment B raw9417step0 raw9417step0Labels := by
      have ha : raw9417step0 = (fun i j => raw9417 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9417step0 raw9417; decide +kernel
      have hl : raw9417step0Labels = raw9417Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9417 raw9417Labels permutation152 permutation3
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw9418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9418step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw9418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9418 raw9418Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw9418 raw9418Labels = mixedMoment B raw9418step0 raw9418step0Labels := by
      have hz : ∀ j, raw9418 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9418step0 = (fun i j => raw9418 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9418step0 raw9418; decide +kernel
      have hl : raw9418step0Labels = raw9418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9418 raw9418Labels permutation265 hz
    mixedMoment B raw9418step0 raw9418step0Labels = mixedMoment B raw9418step1 raw9418step1Labels := by
      have ha : raw9418step1 = (fun i j => raw9418step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9418step1 raw9418step0; decide +kernel
      have hl : raw9418step1Labels = raw9418step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9418step0 raw9418step0Labels permutation32 permutation3
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw9419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9419step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw9419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9419 raw9419Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw9419 raw9419Labels = mixedMoment B raw9419step0 raw9419step0Labels := by
      have hz : ∀ j, raw9419 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9419step0 = (fun i j => raw9419 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9419step0 raw9419; decide +kernel
      have hl : raw9419step0Labels = raw9419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9419 raw9419Labels permutation265 hz
    mixedMoment B raw9419step0 raw9419step0Labels = mixedMoment B raw9419step1 raw9419step1Labels := by
      have ha : raw9419step1 = (fun i j => raw9419step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9419step1 raw9419step0; decide +kernel
      have hl : raw9419step1Labels = raw9419step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9419step0 raw9419step0Labels permutation38 permutation3
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw9420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw9420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw9420step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw9420step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw9420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9420 raw9420Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw9420 raw9420Labels = mixedMoment B raw9420step0 raw9420step0Labels := by
      have hz : ∀ j, raw9420 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9420step0 = (fun i j => raw9420 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9420step0 raw9420; decide +kernel
      have hl : raw9420step0Labels = raw9420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9420 raw9420Labels permutation520 hz
    mixedMoment B raw9420step0 raw9420step0Labels = mixedMoment B raw9420step1 raw9420step1Labels := by
      have hz : ∀ j, raw9420step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9420step1 = (fun i j => raw9420step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9420step1 raw9420step0; decide +kernel
      have hl : raw9420step1Labels = raw9420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9420step0 raw9420step0Labels permutation56 hz
    mixedMoment B raw9420step1 raw9420step1Labels = mixedMoment B raw9420step2 raw9420step2Labels := by
      have ha : raw9420step2 = (fun i j => raw9420step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9420step2 raw9420step1; decide +kernel
      have hl : raw9420step2Labels = raw9420step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9420step1 raw9420step1Labels permutation8 permutation3
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw9421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9421Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9421step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9421 raw9421Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw9421 raw9421Labels = mixedMoment B raw9421step0 raw9421step0Labels := by
      have ha : raw9421step0 = (fun i j => raw9421 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9421step0 raw9421; decide +kernel
      have hl : raw9421step0Labels = raw9421Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9421 raw9421Labels permutation674 permutation7
    mixedMoment B raw9421step0 raw9421step0Labels = mixedMoment B raw9421step1 raw9421step1Labels := by
      have ha : raw9421step1 = raw9421step0 := by apply Matrix.ext; unfold raw9421step1 raw9421step0; decide +kernel
      have hl : raw9421step0Labels = labelEmbedding1 ∘ raw9421step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9421step0 raw9421step0Labels raw9421step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2720 node2720Labels := by rfl

def raw9422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9422step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9422step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9422 raw9422Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw9422 raw9422Labels = mixedMoment B raw9422step0 raw9422step0Labels := by
      have hz : ∀ j, raw9422 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9422step0 = (fun i j => raw9422 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9422step0 raw9422; decide +kernel
      have hl : raw9422step0Labels = raw9422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9422 raw9422Labels permutation265 hz
    mixedMoment B raw9422step0 raw9422step0Labels = mixedMoment B raw9422step1 raw9422step1Labels := by
      have ha : raw9422step1 = (fun i j => raw9422step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9422step1 raw9422step0; decide +kernel
      have hl : raw9422step1Labels = raw9422step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9422step0 raw9422step0Labels permutation151 permutation7
    mixedMoment B raw9422step1 raw9422step1Labels = mixedMoment B raw9422step2 raw9422step2Labels := by
      have ha : raw9422step2 = raw9422step1 := by apply Matrix.ext; unfold raw9422step2 raw9422step1; decide +kernel
      have hl : raw9422step1Labels = labelEmbedding1 ∘ raw9422step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9422step1 raw9422step1Labels raw9422step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw9423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9423Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9423step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9423step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9423 raw9423Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw9423 raw9423Labels = mixedMoment B raw9423step0 raw9423step0Labels := by
      have hz : ∀ j, raw9423 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9423step0 = (fun i j => raw9423 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9423step0 raw9423; decide +kernel
      have hl : raw9423step0Labels = raw9423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9423 raw9423Labels permutation265 hz
    mixedMoment B raw9423step0 raw9423step0Labels = mixedMoment B raw9423step1 raw9423step1Labels := by
      have ha : raw9423step1 = (fun i j => raw9423step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9423step1 raw9423step0; decide +kernel
      have hl : raw9423step1Labels = raw9423step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9423step0 raw9423step0Labels permutation149 permutation7
    mixedMoment B raw9423step1 raw9423step1Labels = mixedMoment B raw9423step2 raw9423step2Labels := by
      have ha : raw9423step2 = raw9423step1 := by apply Matrix.ext; unfold raw9423step2 raw9423step1; decide +kernel
      have hl : raw9423step1Labels = labelEmbedding1 ∘ raw9423step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9423step1 raw9423step1Labels raw9423step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw9424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9424step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9424step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9424step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9424step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9424step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9424step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9424 raw9424Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw9424 raw9424Labels = mixedMoment B raw9424step0 raw9424step0Labels := by
      have hz : ∀ j, raw9424 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9424step0 = (fun i j => raw9424 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9424step0 raw9424; decide +kernel
      have hl : raw9424step0Labels = raw9424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9424 raw9424Labels permutation520 hz
    mixedMoment B raw9424step0 raw9424step0Labels = mixedMoment B raw9424step1 raw9424step1Labels := by
      have hz : ∀ j, raw9424step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9424step1 = (fun i j => raw9424step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9424step1 raw9424step0; decide +kernel
      have hl : raw9424step1Labels = raw9424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9424step0 raw9424step0Labels permutation56 hz
    mixedMoment B raw9424step1 raw9424step1Labels = mixedMoment B raw9424step2 raw9424step2Labels := by
      have ha : raw9424step2 = (fun i j => raw9424step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9424step2 raw9424step1; decide +kernel
      have hl : raw9424step2Labels = raw9424step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9424step1 raw9424step1Labels permutation29 permutation7
    mixedMoment B raw9424step2 raw9424step2Labels = mixedMoment B raw9424step3 raw9424step3Labels := by
      have ha : raw9424step3 = raw9424step2 := by apply Matrix.ext; unfold raw9424step3 raw9424step2; decide +kernel
      have hl : raw9424step2Labels = labelEmbedding1 ∘ raw9424step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9424step2 raw9424step2Labels raw9424step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw9425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9425step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9425 raw9425Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw9425 raw9425Labels = mixedMoment B raw9425step0 raw9425step0Labels := by
      have hz : ∀ j, raw9425 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9425step0 = (fun i j => raw9425 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9425step0 raw9425; decide +kernel
      have hl : raw9425step0Labels = raw9425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9425 raw9425Labels permutation265 hz
    mixedMoment B raw9425step0 raw9425step0Labels = mixedMoment B raw9425step1 raw9425step1Labels := by
      have ha : raw9425step1 = (fun i j => raw9425step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9425step1 raw9425step0; decide +kernel
      have hl : raw9425step1Labels = raw9425step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9425step0 raw9425step0Labels permutation149 permutation7
    mixedMoment B raw9425step1 raw9425step1Labels = mixedMoment B raw9425step2 raw9425step2Labels := by
      have ha : raw9425step2 = raw9425step1 := by apply Matrix.ext; unfold raw9425step2 raw9425step1; decide +kernel
      have hl : raw9425step1Labels = labelEmbedding1 ∘ raw9425step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9425step1 raw9425step1Labels raw9425step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw9426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9426step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9426step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9426 raw9426Labels = mixedMoment B node1654 node1654Labels := by
  calc
    mixedMoment B raw9426 raw9426Labels = mixedMoment B raw9426step0 raw9426step0Labels := by
      have ha : raw9426step0 = (fun i j => raw9426 (permutation254 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9426step0 raw9426; decide +kernel
      have hl : raw9426step0Labels = raw9426Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9426 raw9426Labels permutation254 permutation5
    mixedMoment B raw9426step0 raw9426step0Labels = mixedMoment B raw9426step1 raw9426step1Labels := by
      have ha : raw9426step1 = -raw9426step0 := by apply Matrix.ext; change ∀ i j, raw9426step1 i j = -(raw9426step0 i j); unfold raw9426step1 raw9426step0; decide +kernel
      have hl : raw9426step1Labels = raw9426step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9426step1 raw9426step1Labels = mixedMoment B raw9426step2 raw9426step2Labels := by
      have ha : raw9426step2 = raw9426step1 := by apply Matrix.ext; unfold raw9426step2 raw9426step1; decide +kernel
      have hl : raw9426step1Labels = labelEmbedding1 ∘ raw9426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9426step1 raw9426step1Labels raw9426step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1654 node1654Labels := by rfl

def raw9427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9427Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9427step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9427 raw9427Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw9427 raw9427Labels = mixedMoment B raw9427step0 raw9427step0Labels := by
      have ha : raw9427step0 = (fun i j => raw9427 (permutation622 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9427step0 raw9427; decide +kernel
      have hl : raw9427step0Labels = raw9427Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9427 raw9427Labels permutation622 permutation7
    mixedMoment B raw9427step0 raw9427step0Labels = mixedMoment B raw9427step1 raw9427step1Labels := by
      have ha : raw9427step1 = raw9427step0 := by apply Matrix.ext; unfold raw9427step1 raw9427step0; decide +kernel
      have hl : raw9427step0Labels = labelEmbedding1 ∘ raw9427step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9427step0 raw9427step0Labels raw9427step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw9428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9428step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9428 raw9428Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw9428 raw9428Labels = mixedMoment B raw9428step0 raw9428step0Labels := by
      have ha : raw9428step0 = (fun i j => raw9428 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9428step0 raw9428; decide +kernel
      have hl : raw9428step0Labels = raw9428Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9428 raw9428Labels permutation620 permutation7
    mixedMoment B raw9428step0 raw9428step0Labels = mixedMoment B raw9428step1 raw9428step1Labels := by
      have ha : raw9428step1 = raw9428step0 := by apply Matrix.ext; unfold raw9428step1 raw9428step0; decide +kernel
      have hl : raw9428step0Labels = labelEmbedding1 ∘ raw9428step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9428step0 raw9428step0Labels raw9428step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw9429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9429step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9429step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9429 raw9429Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw9429 raw9429Labels = mixedMoment B raw9429step0 raw9429step0Labels := by
      have hz : ∀ j, raw9429 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9429step0 = (fun i j => raw9429 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9429step0 raw9429; decide +kernel
      have hl : raw9429step0Labels = raw9429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9429 raw9429Labels permutation520 hz
    mixedMoment B raw9429step0 raw9429step0Labels = mixedMoment B raw9429step1 raw9429step1Labels := by
      have ha : raw9429step1 = (fun i j => raw9429step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9429step1 raw9429step0; decide +kernel
      have hl : raw9429step1Labels = raw9429step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9429step0 raw9429step0Labels permutation137 permutation7
    mixedMoment B raw9429step1 raw9429step1Labels = mixedMoment B raw9429step2 raw9429step2Labels := by
      have ha : raw9429step2 = raw9429step1 := by apply Matrix.ext; unfold raw9429step2 raw9429step1; decide +kernel
      have hl : raw9429step1Labels = labelEmbedding1 ∘ raw9429step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9429step1 raw9429step1Labels raw9429step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw9430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9430step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9430step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9430 raw9430Labels = mixedMoment B node3073 node3073Labels := by
  calc
    mixedMoment B raw9430 raw9430Labels = mixedMoment B raw9430step0 raw9430step0Labels := by
      have ha : raw9430step0 = (fun i j => raw9430 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9430step0 raw9430; decide +kernel
      have hl : raw9430step0Labels = raw9430Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9430 raw9430Labels permutation620 permutation7
    mixedMoment B raw9430step0 raw9430step0Labels = mixedMoment B raw9430step1 raw9430step1Labels := by
      have ha : raw9430step1 = raw9430step0 := by apply Matrix.ext; unfold raw9430step1 raw9430step0; decide +kernel
      have hl : raw9430step0Labels = labelEmbedding1 ∘ raw9430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9430step0 raw9430step0Labels raw9430step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3073 node3073Labels := by rfl

def raw9431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw9431step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9431step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9431step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9431step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9431 raw9431Labels = mixedMoment B node1656 node1656Labels := by
  calc
    mixedMoment B raw9431 raw9431Labels = mixedMoment B raw9431step0 raw9431step0Labels := by
      have hz : ∀ j, raw9431 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9431step0 = (fun i j => raw9431 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9431step0 raw9431; decide +kernel
      have hl : raw9431step0Labels = raw9431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9431 raw9431Labels permutation265 hz
    mixedMoment B raw9431step0 raw9431step0Labels = mixedMoment B raw9431step1 raw9431step1Labels := by
      have ha : raw9431step1 = (fun i j => raw9431step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9431step1 raw9431step0; decide +kernel
      have hl : raw9431step1Labels = raw9431step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9431step0 raw9431step0Labels permutation53 permutation5
    mixedMoment B raw9431step1 raw9431step1Labels = mixedMoment B raw9431step2 raw9431step2Labels := by
      have ha : raw9431step2 = -raw9431step1 := by apply Matrix.ext; change ∀ i j, raw9431step2 i j = -(raw9431step1 i j); unfold raw9431step2 raw9431step1; decide +kernel
      have hl : raw9431step2Labels = raw9431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9431step2 raw9431step2Labels = mixedMoment B raw9431step3 raw9431step3Labels := by
      have ha : raw9431step3 = raw9431step2 := by apply Matrix.ext; unfold raw9431step3 raw9431step2; decide +kernel
      have hl : raw9431step2Labels = labelEmbedding1 ∘ raw9431step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9431step2 raw9431step2Labels raw9431step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1656 node1656Labels := by rfl

def raw9432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9432step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9432 raw9432Labels = mixedMoment B node2717 node2717Labels := by
  calc
    mixedMoment B raw9432 raw9432Labels = mixedMoment B raw9432step0 raw9432step0Labels := by
      have ha : raw9432step0 = (fun i j => raw9432 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9432step0 raw9432; decide +kernel
      have hl : raw9432step0Labels = raw9432Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9432 raw9432Labels permutation674 permutation7
    mixedMoment B raw9432step0 raw9432step0Labels = mixedMoment B raw9432step1 raw9432step1Labels := by
      have ha : raw9432step1 = raw9432step0 := by apply Matrix.ext; unfold raw9432step1 raw9432step0; decide +kernel
      have hl : raw9432step0Labels = labelEmbedding1 ∘ raw9432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9432step0 raw9432step0Labels raw9432step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2717 node2717Labels := by rfl

def raw9433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9433Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9433step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw9433step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9433step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw9433step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9433 raw9433Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw9433 raw9433Labels = mixedMoment B raw9433step0 raw9433step0Labels := by
      have hz : ∀ j, raw9433 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9433step0 = (fun i j => raw9433 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9433step0 raw9433; decide +kernel
      have hl : raw9433step0Labels = raw9433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9433 raw9433Labels permutation265 hz
    mixedMoment B raw9433step0 raw9433step0Labels = mixedMoment B raw9433step1 raw9433step1Labels := by
      have ha : raw9433step1 = (fun i j => raw9433step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9433step1 raw9433step0; decide +kernel
      have hl : raw9433step1Labels = raw9433step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9433step0 raw9433step0Labels permutation149 permutation7
    mixedMoment B raw9433step1 raw9433step1Labels = mixedMoment B raw9433step2 raw9433step2Labels := by
      have ha : raw9433step2 = raw9433step1 := by apply Matrix.ext; unfold raw9433step2 raw9433step1; decide +kernel
      have hl : raw9433step1Labels = labelEmbedding1 ∘ raw9433step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9433step1 raw9433step1Labels raw9433step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw9434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9434step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9434step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9434step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9434step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9434step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9434step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9434 raw9434Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw9434 raw9434Labels = mixedMoment B raw9434step0 raw9434step0Labels := by
      have hz : ∀ j, raw9434 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9434step0 = (fun i j => raw9434 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9434step0 raw9434; decide +kernel
      have hl : raw9434step0Labels = raw9434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9434 raw9434Labels permutation520 hz
    mixedMoment B raw9434step0 raw9434step0Labels = mixedMoment B raw9434step1 raw9434step1Labels := by
      have hz : ∀ j, raw9434step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9434step1 = (fun i j => raw9434step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9434step1 raw9434step0; decide +kernel
      have hl : raw9434step1Labels = raw9434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9434step0 raw9434step0Labels permutation56 hz
    mixedMoment B raw9434step1 raw9434step1Labels = mixedMoment B raw9434step2 raw9434step2Labels := by
      have ha : raw9434step2 = (fun i j => raw9434step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9434step2 raw9434step1; decide +kernel
      have hl : raw9434step2Labels = raw9434step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9434step1 raw9434step1Labels permutation29 permutation7
    mixedMoment B raw9434step2 raw9434step2Labels = mixedMoment B raw9434step3 raw9434step3Labels := by
      have ha : raw9434step3 = raw9434step2 := by apply Matrix.ext; unfold raw9434step3 raw9434step2; decide +kernel
      have hl : raw9434step2Labels = labelEmbedding1 ∘ raw9434step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9434step2 raw9434step2Labels raw9434step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw9435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9435 raw9435Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw9435 raw9435Labels = mixedMoment B raw9435step0 raw9435step0Labels := by
      have hz : ∀ j, raw9435 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9435step0 = (fun i j => raw9435 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9435step0 raw9435; decide +kernel
      have hl : raw9435step0Labels = raw9435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9435 raw9435Labels permutation265 hz
    mixedMoment B raw9435step0 raw9435step0Labels = mixedMoment B raw9435step1 raw9435step1Labels := by
      have ha : raw9435step1 = (fun i j => raw9435step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9435step1 raw9435step0; decide +kernel
      have hl : raw9435step1Labels = raw9435step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9435step0 raw9435step0Labels permutation149 permutation7
    mixedMoment B raw9435step1 raw9435step1Labels = mixedMoment B raw9435step2 raw9435step2Labels := by
      have ha : raw9435step2 = raw9435step1 := by apply Matrix.ext; unfold raw9435step2 raw9435step1; decide +kernel
      have hl : raw9435step1Labels = labelEmbedding1 ∘ raw9435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9435step1 raw9435step1Labels raw9435step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3096 node3096Labels := by rfl

def raw9436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9436step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw9436step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9436step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9436step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9436step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9436 raw9436Labels = mixedMoment B node1656 node1656Labels := by
  calc
    mixedMoment B raw9436 raw9436Labels = mixedMoment B raw9436step0 raw9436step0Labels := by
      have hz : ∀ j, raw9436 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9436step0 = (fun i j => raw9436 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9436step0 raw9436; decide +kernel
      have hl : raw9436step0Labels = raw9436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9436 raw9436Labels permutation265 hz
    mixedMoment B raw9436step0 raw9436step0Labels = mixedMoment B raw9436step1 raw9436step1Labels := by
      have ha : raw9436step1 = (fun i j => raw9436step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9436step1 raw9436step0; decide +kernel
      have hl : raw9436step1Labels = raw9436step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9436step0 raw9436step0Labels permutation51 permutation5
    mixedMoment B raw9436step1 raw9436step1Labels = mixedMoment B raw9436step2 raw9436step2Labels := by
      have ha : raw9436step2 = -raw9436step1 := by apply Matrix.ext; change ∀ i j, raw9436step2 i j = -(raw9436step1 i j); unfold raw9436step2 raw9436step1; decide +kernel
      have hl : raw9436step2Labels = raw9436step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9436step2 raw9436step2Labels = mixedMoment B raw9436step3 raw9436step3Labels := by
      have ha : raw9436step3 = raw9436step2 := by apply Matrix.ext; unfold raw9436step3 raw9436step2; decide +kernel
      have hl : raw9436step2Labels = labelEmbedding1 ∘ raw9436step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9436step2 raw9436step2Labels raw9436step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1656 node1656Labels := by rfl

def raw9437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9437step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9437 raw9437Labels = mixedMoment B node2717 node2717Labels := by
  calc
    mixedMoment B raw9437 raw9437Labels = mixedMoment B raw9437step0 raw9437step0Labels := by
      have ha : raw9437step0 = (fun i j => raw9437 (permutation676 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9437step0 raw9437; decide +kernel
      have hl : raw9437step0Labels = raw9437Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9437 raw9437Labels permutation676 permutation7
    mixedMoment B raw9437step0 raw9437step0Labels = mixedMoment B raw9437step1 raw9437step1Labels := by
      have ha : raw9437step1 = raw9437step0 := by apply Matrix.ext; unfold raw9437step1 raw9437step0; decide +kernel
      have hl : raw9437step0Labels = labelEmbedding1 ∘ raw9437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9437step0 raw9437step0Labels raw9437step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2717 node2717Labels := by rfl

def raw9438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9438step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw9438step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw9438step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9438 raw9438Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw9438 raw9438Labels = mixedMoment B raw9438step0 raw9438step0Labels := by
      have hz : ∀ j, raw9438 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9438step0 = (fun i j => raw9438 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9438step0 raw9438; decide +kernel
      have hl : raw9438step0Labels = raw9438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9438 raw9438Labels permutation265 hz
    mixedMoment B raw9438step0 raw9438step0Labels = mixedMoment B raw9438step1 raw9438step1Labels := by
      have ha : raw9438step1 = (fun i j => raw9438step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9438step1 raw9438step0; decide +kernel
      have hl : raw9438step1Labels = raw9438step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9438step0 raw9438step0Labels permutation151 permutation7
    mixedMoment B raw9438step1 raw9438step1Labels = mixedMoment B raw9438step2 raw9438step2Labels := by
      have ha : raw9438step2 = raw9438step1 := by apply Matrix.ext; unfold raw9438step2 raw9438step1; decide +kernel
      have hl : raw9438step1Labels = labelEmbedding1 ∘ raw9438step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9438step1 raw9438step1Labels raw9438step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw9439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw9439step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9439step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9439step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9439step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9439step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9439 raw9439Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw9439 raw9439Labels = mixedMoment B raw9439step0 raw9439step0Labels := by
      have hz : ∀ j, raw9439 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9439step0 = (fun i j => raw9439 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9439step0 raw9439; decide +kernel
      have hl : raw9439step0Labels = raw9439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9439 raw9439Labels permutation520 hz
    mixedMoment B raw9439step0 raw9439step0Labels = mixedMoment B raw9439step1 raw9439step1Labels := by
      have hz : ∀ j, raw9439step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9439step1 = (fun i j => raw9439step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9439step1 raw9439step0; decide +kernel
      have hl : raw9439step1Labels = raw9439step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9439step0 raw9439step0Labels permutation56 hz
    mixedMoment B raw9439step1 raw9439step1Labels = mixedMoment B raw9439step2 raw9439step2Labels := by
      have ha : raw9439step2 = (fun i j => raw9439step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9439step2 raw9439step1; decide +kernel
      have hl : raw9439step2Labels = raw9439step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9439step1 raw9439step1Labels permutation31 permutation7
    mixedMoment B raw9439step2 raw9439step2Labels = mixedMoment B raw9439step3 raw9439step3Labels := by
      have ha : raw9439step3 = raw9439step2 := by apply Matrix.ext; unfold raw9439step3 raw9439step2; decide +kernel
      have hl : raw9439step2Labels = labelEmbedding1 ∘ raw9439step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9439step2 raw9439step2Labels raw9439step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw9440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9440step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9440step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9440 raw9440Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw9440 raw9440Labels = mixedMoment B raw9440step0 raw9440step0Labels := by
      have hz : ∀ j, raw9440 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9440step0 = (fun i j => raw9440 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9440step0 raw9440; decide +kernel
      have hl : raw9440step0Labels = raw9440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9440 raw9440Labels permutation265 hz
    mixedMoment B raw9440step0 raw9440step0Labels = mixedMoment B raw9440step1 raw9440step1Labels := by
      have ha : raw9440step1 = (fun i j => raw9440step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9440step1 raw9440step0; decide +kernel
      have hl : raw9440step1Labels = raw9440step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9440step0 raw9440step0Labels permutation151 permutation7
    mixedMoment B raw9440step1 raw9440step1Labels = mixedMoment B raw9440step2 raw9440step2Labels := by
      have ha : raw9440step2 = raw9440step1 := by apply Matrix.ext; unfold raw9440step2 raw9440step1; decide +kernel
      have hl : raw9440step1Labels = labelEmbedding1 ∘ raw9440step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9440step1 raw9440step1Labels raw9440step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3096 node3096Labels := by rfl

def raw9441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9441step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw9441step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9441step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9441step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9441step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9441 raw9441Labels = mixedMoment B node1655 node1655Labels := by
  calc
    mixedMoment B raw9441 raw9441Labels = mixedMoment B raw9441step0 raw9441step0Labels := by
      have hz : ∀ j, raw9441 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9441step0 = (fun i j => raw9441 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9441step0 raw9441; decide +kernel
      have hl : raw9441step0Labels = raw9441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9441 raw9441Labels permutation265 hz
    mixedMoment B raw9441step0 raw9441step0Labels = mixedMoment B raw9441step1 raw9441step1Labels := by
      have ha : raw9441step1 = (fun i j => raw9441step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9441step1 raw9441step0; decide +kernel
      have hl : raw9441step1Labels = raw9441step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9441step0 raw9441step0Labels permutation50 permutation5
    mixedMoment B raw9441step1 raw9441step1Labels = mixedMoment B raw9441step2 raw9441step2Labels := by
      have ha : raw9441step2 = -raw9441step1 := by apply Matrix.ext; change ∀ i j, raw9441step2 i j = -(raw9441step1 i j); unfold raw9441step2 raw9441step1; decide +kernel
      have hl : raw9441step2Labels = raw9441step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9441step2 raw9441step2Labels = mixedMoment B raw9441step3 raw9441step3Labels := by
      have ha : raw9441step3 = raw9441step2 := by apply Matrix.ext; unfold raw9441step3 raw9441step2; decide +kernel
      have hl : raw9441step2Labels = labelEmbedding1 ∘ raw9441step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9441step2 raw9441step2Labels raw9441step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1655 node1655Labels := by rfl

def raw9442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9442 raw9442Labels = mixedMoment B node2668 node2668Labels := by
  calc
    mixedMoment B raw9442 raw9442Labels = mixedMoment B raw9442step0 raw9442step0Labels := by
      have ha : raw9442step0 = (fun i j => raw9442 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9442step0 raw9442; decide +kernel
      have hl : raw9442step0Labels = raw9442Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9442 raw9442Labels permutation674 permutation7
    mixedMoment B raw9442step0 raw9442step0Labels = mixedMoment B raw9442step1 raw9442step1Labels := by
      have ha : raw9442step1 = raw9442step0 := by apply Matrix.ext; unfold raw9442step1 raw9442step0; decide +kernel
      have hl : raw9442step0Labels = labelEmbedding1 ∘ raw9442step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9442step0 raw9442step0Labels raw9442step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2668 node2668Labels := by rfl

def raw9443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9443step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9443step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9443 raw9443Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw9443 raw9443Labels = mixedMoment B raw9443step0 raw9443step0Labels := by
      have hz : ∀ j, raw9443 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9443step0 = (fun i j => raw9443 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9443step0 raw9443; decide +kernel
      have hl : raw9443step0Labels = raw9443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9443 raw9443Labels permutation265 hz
    mixedMoment B raw9443step0 raw9443step0Labels = mixedMoment B raw9443step1 raw9443step1Labels := by
      have ha : raw9443step1 = (fun i j => raw9443step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9443step1 raw9443step0; decide +kernel
      have hl : raw9443step1Labels = raw9443step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9443step0 raw9443step0Labels permutation151 permutation7
    mixedMoment B raw9443step1 raw9443step1Labels = mixedMoment B raw9443step2 raw9443step2Labels := by
      have ha : raw9443step2 = raw9443step1 := by apply Matrix.ext; unfold raw9443step2 raw9443step1; decide +kernel
      have hl : raw9443step1Labels = labelEmbedding1 ∘ raw9443step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9443step1 raw9443step1Labels raw9443step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw9444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9444 raw9444Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw9444 raw9444Labels = mixedMoment B raw9444step0 raw9444step0Labels := by
      have hz : ∀ j, raw9444 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9444step0 = (fun i j => raw9444 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9444step0 raw9444; decide +kernel
      have hl : raw9444step0Labels = raw9444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9444 raw9444Labels permutation265 hz
    mixedMoment B raw9444step0 raw9444step0Labels = mixedMoment B raw9444step1 raw9444step1Labels := by
      have ha : raw9444step1 = (fun i j => raw9444step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9444step1 raw9444step0; decide +kernel
      have hl : raw9444step1Labels = raw9444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9444step0 raw9444step0Labels permutation149 permutation7
    mixedMoment B raw9444step1 raw9444step1Labels = mixedMoment B raw9444step2 raw9444step2Labels := by
      have ha : raw9444step2 = raw9444step1 := by apply Matrix.ext; unfold raw9444step2 raw9444step1; decide +kernel
      have hl : raw9444step1Labels = labelEmbedding1 ∘ raw9444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9444step1 raw9444step1Labels raw9444step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw9445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw9445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9445 raw9445Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw9445 raw9445Labels = mixedMoment B raw9445step0 raw9445step0Labels := by
      have hz : ∀ j, raw9445 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9445step0 = (fun i j => raw9445 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9445step0 raw9445; decide +kernel
      have hl : raw9445step0Labels = raw9445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9445 raw9445Labels permutation265 hz
    mixedMoment B raw9445step0 raw9445step0Labels = mixedMoment B raw9445step1 raw9445step1Labels := by
      have ha : raw9445step1 = (fun i j => raw9445step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9445step1 raw9445step0; decide +kernel
      have hl : raw9445step1Labels = raw9445step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9445step0 raw9445step0Labels permutation149 permutation7
    mixedMoment B raw9445step1 raw9445step1Labels = mixedMoment B raw9445step2 raw9445step2Labels := by
      have ha : raw9445step2 = raw9445step1 := by apply Matrix.ext; unfold raw9445step2 raw9445step1; decide +kernel
      have hl : raw9445step1Labels = labelEmbedding1 ∘ raw9445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9445step1 raw9445step1Labels raw9445step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3050 node3050Labels := by rfl

def raw9446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9446step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9446step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9446 raw9446Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw9446 raw9446Labels = mixedMoment B raw9446step0 raw9446step0Labels := by
      have hz : ∀ j, raw9446 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9446step0 = (fun i j => raw9446 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9446step0 raw9446; decide +kernel
      have hl : raw9446step0Labels = raw9446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9446 raw9446Labels permutation265 hz
    mixedMoment B raw9446step0 raw9446step0Labels = mixedMoment B raw9446step1 raw9446step1Labels := by
      have ha : raw9446step1 = (fun i j => raw9446step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9446step1 raw9446step0; decide +kernel
      have hl : raw9446step1Labels = raw9446step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9446step0 raw9446step0Labels permutation50 permutation5
    mixedMoment B raw9446step1 raw9446step1Labels = mixedMoment B raw9446step2 raw9446step2Labels := by
      have ha : raw9446step2 = -raw9446step1 := by apply Matrix.ext; change ∀ i j, raw9446step2 i j = -(raw9446step1 i j); unfold raw9446step2 raw9446step1; decide +kernel
      have hl : raw9446step2Labels = raw9446step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9446step2 raw9446step2Labels = mixedMoment B raw9446step3 raw9446step3Labels := by
      have ha : raw9446step3 = raw9446step2 := by apply Matrix.ext; unfold raw9446step3 raw9446step2; decide +kernel
      have hl : raw9446step2Labels = labelEmbedding1 ∘ raw9446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9446step2 raw9446step2Labels raw9446step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw9447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9447step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9447 raw9447Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw9447 raw9447Labels = mixedMoment B raw9447step0 raw9447step0Labels := by
      have ha : raw9447step0 = (fun i j => raw9447 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9447step0 raw9447; decide +kernel
      have hl : raw9447step0Labels = raw9447Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9447 raw9447Labels permutation674 permutation7
    mixedMoment B raw9447step0 raw9447step0Labels = mixedMoment B raw9447step1 raw9447step1Labels := by
      have ha : raw9447step1 = raw9447step0 := by apply Matrix.ext; unfold raw9447step1 raw9447step0; decide +kernel
      have hl : raw9447step0Labels = labelEmbedding1 ∘ raw9447step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9447step0 raw9447step0Labels raw9447step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw9448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9448 raw9448Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw9448 raw9448Labels = mixedMoment B raw9448step0 raw9448step0Labels := by
      have hz : ∀ j, raw9448 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9448step0 = (fun i j => raw9448 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9448step0 raw9448; decide +kernel
      have hl : raw9448step0Labels = raw9448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9448 raw9448Labels permutation265 hz
    mixedMoment B raw9448step0 raw9448step0Labels = mixedMoment B raw9448step1 raw9448step1Labels := by
      have ha : raw9448step1 = (fun i j => raw9448step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9448step1 raw9448step0; decide +kernel
      have hl : raw9448step1Labels = raw9448step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9448step0 raw9448step0Labels permutation151 permutation7
    mixedMoment B raw9448step1 raw9448step1Labels = mixedMoment B raw9448step2 raw9448step2Labels := by
      have ha : raw9448step2 = raw9448step1 := by apply Matrix.ext; unfold raw9448step2 raw9448step1; decide +kernel
      have hl : raw9448step1Labels = labelEmbedding1 ∘ raw9448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9448step1 raw9448step1Labels raw9448step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw9449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9449 raw9449Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw9449 raw9449Labels = mixedMoment B raw9449step0 raw9449step0Labels := by
      have hz : ∀ j, raw9449 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9449step0 = (fun i j => raw9449 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9449step0 raw9449; decide +kernel
      have hl : raw9449step0Labels = raw9449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9449 raw9449Labels permutation265 hz
    mixedMoment B raw9449step0 raw9449step0Labels = mixedMoment B raw9449step1 raw9449step1Labels := by
      have ha : raw9449step1 = (fun i j => raw9449step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9449step1 raw9449step0; decide +kernel
      have hl : raw9449step1Labels = raw9449step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9449step0 raw9449step0Labels permutation149 permutation7
    mixedMoment B raw9449step1 raw9449step1Labels = mixedMoment B raw9449step2 raw9449step2Labels := by
      have ha : raw9449step2 = raw9449step1 := by apply Matrix.ext; unfold raw9449step2 raw9449step1; decide +kernel
      have hl : raw9449step1Labels = labelEmbedding1 ∘ raw9449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9449step1 raw9449step1Labels raw9449step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw9450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw9450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw9450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw9450step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9450step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9450step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9450 raw9450Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw9450 raw9450Labels = mixedMoment B raw9450step0 raw9450step0Labels := by
      have hz : ∀ j, raw9450 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9450step0 = (fun i j => raw9450 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9450step0 raw9450; decide +kernel
      have hl : raw9450step0Labels = raw9450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9450 raw9450Labels permutation520 hz
    mixedMoment B raw9450step0 raw9450step0Labels = mixedMoment B raw9450step1 raw9450step1Labels := by
      have hz : ∀ j, raw9450step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9450step1 = (fun i j => raw9450step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9450step1 raw9450step0; decide +kernel
      have hl : raw9450step1Labels = raw9450step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9450step0 raw9450step0Labels permutation56 hz
    mixedMoment B raw9450step1 raw9450step1Labels = mixedMoment B raw9450step2 raw9450step2Labels := by
      have ha : raw9450step2 = (fun i j => raw9450step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9450step2 raw9450step1; decide +kernel
      have hl : raw9450step2Labels = raw9450step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9450step1 raw9450step1Labels permutation29 permutation7
    mixedMoment B raw9450step2 raw9450step2Labels = mixedMoment B raw9450step3 raw9450step3Labels := by
      have ha : raw9450step3 = raw9450step2 := by apply Matrix.ext; unfold raw9450step3 raw9450step2; decide +kernel
      have hl : raw9450step2Labels = labelEmbedding1 ∘ raw9450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9450step2 raw9450step2Labels raw9450step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw9451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9451 raw9451Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw9451 raw9451Labels = mixedMoment B raw9451step0 raw9451step0Labels := by
      have hz : ∀ j, raw9451 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9451step0 = (fun i j => raw9451 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9451step0 raw9451; decide +kernel
      have hl : raw9451step0Labels = raw9451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9451 raw9451Labels permutation265 hz
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw9452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9452 raw9452Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw9452 raw9452Labels = mixedMoment B raw9452step0 raw9452step0Labels := by
      have ha : raw9452step0 = (fun i j => raw9452 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9452step0 raw9452; decide +kernel
      have hl : raw9452step0Labels = raw9452Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9452 raw9452Labels permutation682 permutation2
    mixedMoment B raw9452step0 raw9452step0Labels = mixedMoment B raw9452step1 raw9452step1Labels := by
      have ha : raw9452step1 = -raw9452step0 := by apply Matrix.ext; change ∀ i j, raw9452step1 i j = -(raw9452step0 i j); unfold raw9452step1 raw9452step0; decide +kernel
      have hl : raw9452step1Labels = raw9452step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3525 node3525Labels := by rfl

def raw9453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9453 raw9453Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw9453 raw9453Labels = mixedMoment B raw9453step0 raw9453step0Labels := by
      have hz : ∀ j, raw9453 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9453step0 = (fun i j => raw9453 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9453step0 raw9453; decide +kernel
      have hl : raw9453step0Labels = raw9453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9453 raw9453Labels permutation265 hz
    mixedMoment B raw9453step0 raw9453step0Labels = mixedMoment B raw9453step1 raw9453step1Labels := by
      have ha : raw9453step1 = (fun i j => raw9453step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9453step1 raw9453step0; decide +kernel
      have hl : raw9453step1Labels = raw9453step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9453step0 raw9453step0Labels permutation151 permutation2
    mixedMoment B raw9453step1 raw9453step1Labels = mixedMoment B raw9453step2 raw9453step2Labels := by
      have ha : raw9453step2 = -raw9453step1 := by apply Matrix.ext; change ∀ i j, raw9453step2 i j = -(raw9453step1 i j); unfold raw9453step2 raw9453step1; decide +kernel
      have hl : raw9453step2Labels = raw9453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw9454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9454 raw9454Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw9454 raw9454Labels = mixedMoment B raw9454step0 raw9454step0Labels := by
      have hz : ∀ j, raw9454 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9454step0 = (fun i j => raw9454 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9454step0 raw9454; decide +kernel
      have hl : raw9454step0Labels = raw9454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9454 raw9454Labels permutation265 hz
    mixedMoment B raw9454step0 raw9454step0Labels = mixedMoment B raw9454step1 raw9454step1Labels := by
      have ha : raw9454step1 = (fun i j => raw9454step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9454step1 raw9454step0; decide +kernel
      have hl : raw9454step1Labels = raw9454step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9454step0 raw9454step0Labels permutation149 permutation2
    mixedMoment B raw9454step1 raw9454step1Labels = mixedMoment B raw9454step2 raw9454step2Labels := by
      have ha : raw9454step2 = -raw9454step1 := by apply Matrix.ext; change ∀ i j, raw9454step2 i j = -(raw9454step1 i j); unfold raw9454step2 raw9454step1; decide +kernel
      have hl : raw9454step2Labels = raw9454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw9455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw9455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9455step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw9455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9455 raw9455Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw9455 raw9455Labels = mixedMoment B raw9455step0 raw9455step0Labels := by
      have hz : ∀ j, raw9455 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9455step0 = (fun i j => raw9455 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9455step0 raw9455; decide +kernel
      have hl : raw9455step0Labels = raw9455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9455 raw9455Labels permutation520 hz
    mixedMoment B raw9455step0 raw9455step0Labels = mixedMoment B raw9455step1 raw9455step1Labels := by
      have hz : ∀ j, raw9455step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9455step1 = (fun i j => raw9455step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9455step1 raw9455step0; decide +kernel
      have hl : raw9455step1Labels = raw9455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9455step0 raw9455step0Labels permutation56 hz
    mixedMoment B raw9455step1 raw9455step1Labels = mixedMoment B raw9455step2 raw9455step2Labels := by
      have ha : raw9455step2 = (fun i j => raw9455step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9455step2 raw9455step1; decide +kernel
      have hl : raw9455step2Labels = raw9455step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9455step1 raw9455step1Labels permutation29 permutation2
    mixedMoment B raw9455step2 raw9455step2Labels = mixedMoment B raw9455step3 raw9455step3Labels := by
      have ha : raw9455step3 = -raw9455step2 := by apply Matrix.ext; change ∀ i j, raw9455step3 i j = -(raw9455step2 i j); unfold raw9455step3 raw9455step2; decide +kernel
      have hl : raw9455step3Labels = raw9455step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3623 node3623Labels := by rfl

def raw9456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9456 raw9456Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw9456 raw9456Labels = mixedMoment B raw9456step0 raw9456step0Labels := by
      have hz : ∀ j, raw9456 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9456step0 = (fun i j => raw9456 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9456step0 raw9456; decide +kernel
      have hl : raw9456step0Labels = raw9456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9456 raw9456Labels permutation265 hz
    mixedMoment B raw9456step0 raw9456step0Labels = mixedMoment B raw9456step1 raw9456step1Labels := by
      have ha : raw9456step1 = (fun i j => raw9456step0 (permutation132 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9456step1 raw9456step0; decide +kernel
      have hl : raw9456step1Labels = raw9456step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9456step0 raw9456step0Labels permutation132 permutation4
    mixedMoment B raw9456step1 raw9456step1Labels = mixedMoment B raw9456step2 raw9456step2Labels := by
      have ha : raw9456step2 = -raw9456step1 := by apply Matrix.ext; change ∀ i j, raw9456step2 i j = -(raw9456step1 i j); unfold raw9456step2 raw9456step1; decide +kernel
      have hl : raw9456step2Labels = raw9456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw9457 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]
def raw9457Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9457step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3]]
def raw9457step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9457step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw9457step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9457step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw9457step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9457step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw9457step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical9457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9457 raw9457Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw9457 raw9457Labels = mixedMoment B raw9457step0 raw9457step0Labels := by
      have hz : ∀ j, raw9457 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9457step0 = (fun i j => raw9457 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9457step0 raw9457; decide +kernel
      have hl : raw9457step0Labels = raw9457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9457 raw9457Labels permutation520 hz
    mixedMoment B raw9457step0 raw9457step0Labels = mixedMoment B raw9457step1 raw9457step1Labels := by
      have hz : ∀ j, raw9457step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9457step1 = (fun i j => raw9457step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9457step1 raw9457step0; decide +kernel
      have hl : raw9457step1Labels = raw9457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9457step0 raw9457step0Labels permutation56 hz
    mixedMoment B raw9457step1 raw9457step1Labels = mixedMoment B raw9457step2 raw9457step2Labels := by
      have ha : raw9457step2 = (fun i j => raw9457step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9457step2 raw9457step1; decide +kernel
      have hl : raw9457step2Labels = raw9457step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9457step1 raw9457step1Labels permutation26 permutation0
    mixedMoment B raw9457step2 raw9457step2Labels = mixedMoment B raw9457step3 raw9457step3Labels := by
      have ha : raw9457step3 = -raw9457step2 := by apply Matrix.ext; change ∀ i j, raw9457step3 i j = -(raw9457step2 i j); unfold raw9457step3 raw9457step2; decide +kernel
      have hl : raw9457step3Labels = raw9457step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw9458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9458 raw9458Labels = mixedMoment B node1382 node1382Labels := by
  calc
    mixedMoment B raw9458 raw9458Labels = mixedMoment B raw9458step0 raw9458step0Labels := by
      have ha : raw9458step0 = (fun i j => raw9458 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9458step0 raw9458; decide +kernel
      have hl : raw9458step0Labels = raw9458Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9458 raw9458Labels permutation182 permutation2
    _ = mixedMoment B node1382 node1382Labels := by rfl

def raw9459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9459 raw9459Labels = mixedMoment B node1404 node1404Labels := by
  calc
    mixedMoment B raw9459 raw9459Labels = mixedMoment B raw9459step0 raw9459step0Labels := by
      have hz : ∀ j, raw9459 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9459step0 = (fun i j => raw9459 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9459step0 raw9459; decide +kernel
      have hl : raw9459step0Labels = raw9459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9459 raw9459Labels permutation265 hz
    mixedMoment B raw9459step0 raw9459step0Labels = mixedMoment B raw9459step1 raw9459step1Labels := by
      have ha : raw9459step1 = (fun i j => raw9459step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9459step1 raw9459step0; decide +kernel
      have hl : raw9459step1Labels = raw9459step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9459step0 raw9459step0Labels permutation38 permutation2
    _ = mixedMoment B node1404 node1404Labels := by rfl

def raw9460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9460 raw9460Labels = mixedMoment B node1404 node1404Labels := by
  calc
    mixedMoment B raw9460 raw9460Labels = mixedMoment B raw9460step0 raw9460step0Labels := by
      have hz : ∀ j, raw9460 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9460step0 = (fun i j => raw9460 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9460step0 raw9460; decide +kernel
      have hl : raw9460step0Labels = raw9460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9460 raw9460Labels permutation265 hz
    _ = mixedMoment B node1404 node1404Labels := by rfl

def raw9461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9461 raw9461Labels = mixedMoment B node1390 node1390Labels := by
  calc
    mixedMoment B raw9461 raw9461Labels = mixedMoment B raw9461step0 raw9461step0Labels := by
      have hz : ∀ j, raw9461 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9461step0 = (fun i j => raw9461 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9461step0 raw9461; decide +kernel
      have hl : raw9461step0Labels = raw9461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9461 raw9461Labels permutation265 hz
    _ = mixedMoment B node1390 node1390Labels := by rfl

def raw9462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9462 raw9462Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw9462 raw9462Labels = mixedMoment B raw9462step0 raw9462step0Labels := by
      have hz : ∀ j, raw9462 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9462step0 = (fun i j => raw9462 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9462step0 raw9462; decide +kernel
      have hl : raw9462step0Labels = raw9462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9462 raw9462Labels permutation265 hz
    _ = mixedMoment B node1385 node1385Labels := by rfl

def raw9463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9463 raw9463Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw9463 raw9463Labels = mixedMoment B raw9463step0 raw9463step0Labels := by
      have ha : raw9463step0 = (fun i j => raw9463 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9463step0 raw9463; decide +kernel
      have hl : raw9463step0Labels = raw9463Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9463 raw9463Labels permutation182 permutation2
    _ = mixedMoment B node2923 node2923Labels := by rfl

def raw9464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9464 raw9464Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw9464 raw9464Labels = mixedMoment B raw9464step0 raw9464step0Labels := by
      have ha : raw9464step0 = (fun i j => raw9464 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9464step0 raw9464; decide +kernel
      have hl : raw9464step0Labels = raw9464Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9464 raw9464Labels permutation206 permutation2
    _ = mixedMoment B node2923 node2923Labels := by rfl

def raw9465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw9465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw9465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9465 raw9465Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw9465 raw9465Labels = mixedMoment B raw9465step0 raw9465step0Labels := by
      have hz : ∀ j, raw9465 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9465step0 = (fun i j => raw9465 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9465step0 raw9465; decide +kernel
      have hl : raw9465step0Labels = raw9465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9465 raw9465Labels permutation520 hz
    mixedMoment B raw9465step0 raw9465step0Labels = mixedMoment B raw9465step1 raw9465step1Labels := by
      have ha : raw9465step1 = (fun i j => raw9465step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9465step1 raw9465step0; decide +kernel
      have hl : raw9465step1Labels = raw9465step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9465step0 raw9465step0Labels permutation40 permutation2
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw9466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw9466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9466 raw9466Labels = mixedMoment B node3073 node3073Labels := by
  calc
    mixedMoment B raw9466 raw9466Labels = mixedMoment B raw9466step0 raw9466step0Labels := by
      have ha : raw9466step0 = (fun i j => raw9466 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9466step0 raw9466; decide +kernel
      have hl : raw9466step0Labels = raw9466Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9466 raw9466Labels permutation182 permutation2
    _ = mixedMoment B node3073 node3073Labels := by rfl

def raw9467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9467 raw9467Labels = mixedMoment B node2983 node2983Labels := by
  calc
    mixedMoment B raw9467 raw9467Labels = mixedMoment B raw9467step0 raw9467step0Labels := by
      have ha : raw9467step0 = (fun i j => raw9467 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9467step0 raw9467; decide +kernel
      have hl : raw9467step0Labels = raw9467Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9467 raw9467Labels permutation158 permutation2
    _ = mixedMoment B node2983 node2983Labels := by rfl

def raw9468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9468 raw9468Labels = mixedMoment B node2983 node2983Labels := by
  calc
    _ = mixedMoment B node2983 node2983Labels := by rfl

def raw9469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw9469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9469 raw9469Labels = mixedMoment B node2980 node2980Labels := by
  calc
    _ = mixedMoment B node2980 node2980Labels := by rfl

def raw9470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw9470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw9470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9470 raw9470Labels = mixedMoment B node2009 node2009Labels := by
  calc
    mixedMoment B raw9470 raw9470Labels = mixedMoment B raw9470step0 raw9470step0Labels := by
      have ha : raw9470step0 = (fun i j => raw9470 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9470step0 raw9470; decide +kernel
      have hl : raw9470step0Labels = raw9470Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9470 raw9470Labels permutation682 permutation2
    mixedMoment B raw9470step0 raw9470step0Labels = mixedMoment B raw9470step1 raw9470step1Labels := by
      have ha : raw9470step1 = -raw9470step0 := by apply Matrix.ext; change ∀ i j, raw9470step1 i j = -(raw9470step0 i j); unfold raw9470step1 raw9470step0; decide +kernel
      have hl : raw9470step1Labels = raw9470step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2009 node2009Labels := by rfl

def raw9471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9471 raw9471Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw9471 raw9471Labels = mixedMoment B raw9471step0 raw9471step0Labels := by
      have hz : ∀ j, raw9471 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9471step0 = (fun i j => raw9471 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9471step0 raw9471; decide +kernel
      have hl : raw9471step0Labels = raw9471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9471 raw9471Labels permutation265 hz
    _ = mixedMoment B node2952 node2952Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
