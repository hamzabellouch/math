import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw41344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41344step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41344step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41344 raw41344Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw41344 raw41344Labels = mixedMoment B raw41344step0 raw41344step0Labels := by
      have hz : ∀ j, raw41344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41344step0 = (fun i j => raw41344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41344step0 raw41344; decide +kernel
      have hl : raw41344step0Labels = raw41344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41344 raw41344Labels permutation434 hz
    mixedMoment B raw41344step0 raw41344step0Labels = mixedMoment B raw41344step1 raw41344step1Labels := by
      have ha : raw41344step1 = (fun i j => raw41344step0 (permutation135 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41344step1 raw41344step0; decide +kernel
      have hl : raw41344step1Labels = raw41344step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41344step0 raw41344step0Labels permutation135 permutation6
    mixedMoment B raw41344step1 raw41344step1Labels = mixedMoment B raw41344step2 raw41344step2Labels := by
      have ha : raw41344step2 = -raw41344step1 := by apply Matrix.ext; change ∀ i j, raw41344step2 i j = -(raw41344step1 i j); unfold raw41344step2 raw41344step1; decide +kernel
      have hl : raw41344step2Labels = raw41344step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw41345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw41345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41345step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw41345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41345 raw41345Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw41345 raw41345Labels = mixedMoment B raw41345step0 raw41345step0Labels := by
      have hz : ∀ j, raw41345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41345step0 = (fun i j => raw41345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41345step0 raw41345; decide +kernel
      have hl : raw41345step0Labels = raw41345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41345 raw41345Labels permutation434 hz
    mixedMoment B raw41345step0 raw41345step0Labels = mixedMoment B raw41345step1 raw41345step1Labels := by
      have ha : raw41345step1 = (fun i j => raw41345step0 (permutation82 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41345step1 raw41345step0; decide +kernel
      have hl : raw41345step1Labels = raw41345step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41345step0 raw41345step0Labels permutation82 permutation6
    _ = mixedMoment B node3903 node3903Labels := by rfl

def raw41346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41346 raw41346Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw41346 raw41346Labels = mixedMoment B raw41346step0 raw41346step0Labels := by
      have ha : raw41346step0 = (fun i j => raw41346 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41346step0 raw41346; decide +kernel
      have hl : raw41346step0Labels = raw41346Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41346 raw41346Labels permutation414 permutation6
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw41347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41347 raw41347Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw41347 raw41347Labels = mixedMoment B raw41347step0 raw41347step0Labels := by
      have ha : raw41347step0 = (fun i j => raw41347 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41347step0 raw41347; decide +kernel
      have hl : raw41347step0Labels = raw41347Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41347 raw41347Labels permutation414 permutation6
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw41348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41348 raw41348Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw41348 raw41348Labels = mixedMoment B raw41348step0 raw41348step0Labels := by
      have ha : raw41348step0 = (fun i j => raw41348 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41348step0 raw41348; decide +kernel
      have hl : raw41348step0Labels = raw41348Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41348 raw41348Labels permutation399 permutation6
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw41349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw41349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41349 raw41349Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw41349 raw41349Labels = mixedMoment B raw41349step0 raw41349step0Labels := by
      have ha : raw41349step0 = (fun i j => raw41349 (permutation359 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41349step0 raw41349; decide +kernel
      have hl : raw41349step0Labels = raw41349Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41349 raw41349Labels permutation359 permutation6
    _ = mixedMoment B node3901 node3901Labels := by rfl

def raw41350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41350Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41350 raw41350Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw41350 raw41350Labels = mixedMoment B raw41350step0 raw41350step0Labels := by
      have ha : raw41350step0 = (fun i j => raw41350 (permutation401 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41350step0 raw41350; decide +kernel
      have hl : raw41350step0Labels = raw41350Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41350 raw41350Labels permutation401 permutation6
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw41351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw41351Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw41351step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41351 raw41351Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw41351 raw41351Labels = mixedMoment B raw41351step0 raw41351step0Labels := by
      have hz : ∀ j, raw41351 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41351step0 = (fun i j => raw41351 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41351step0 raw41351; decide +kernel
      have hl : raw41351step0Labels = raw41351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41351 raw41351Labels permutation434 hz
    mixedMoment B raw41351step0 raw41351step0Labels = mixedMoment B raw41351step1 raw41351step1Labels := by
      have ha : raw41351step1 = (fun i j => raw41351step0 (permutation110 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41351step1 raw41351step0; decide +kernel
      have hl : raw41351step1Labels = raw41351step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41351step0 raw41351step0Labels permutation110 permutation6
    mixedMoment B raw41351step1 raw41351step1Labels = mixedMoment B raw41351step2 raw41351step2Labels := by
      have ha : raw41351step2 = -raw41351step1 := by apply Matrix.ext; change ∀ i j, raw41351step2 i j = -(raw41351step1 i j); unfold raw41351step2 raw41351step1; decide +kernel
      have hl : raw41351step2Labels = raw41351step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw41352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw41352Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -3, 2]]
def raw41352step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41352 raw41352Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw41352 raw41352Labels = mixedMoment B raw41352step0 raw41352step0Labels := by
      have hz : ∀ j, raw41352 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41352step0 = (fun i j => raw41352 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41352step0 raw41352; decide +kernel
      have hl : raw41352step0Labels = raw41352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41352 raw41352Labels permutation434 hz
    mixedMoment B raw41352step0 raw41352step0Labels = mixedMoment B raw41352step1 raw41352step1Labels := by
      have ha : raw41352step1 = (fun i j => raw41352step0 (permutation134 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41352step1 raw41352step0; decide +kernel
      have hl : raw41352step1Labels = raw41352step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41352step0 raw41352step0Labels permutation134 permutation6
    mixedMoment B raw41352step1 raw41352step1Labels = mixedMoment B raw41352step2 raw41352step2Labels := by
      have ha : raw41352step2 = -raw41352step1 := by apply Matrix.ext; change ∀ i j, raw41352step2 i j = -(raw41352step1 i j); unfold raw41352step2 raw41352step1; decide +kernel
      have hl : raw41352step2Labels = raw41352step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw41353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw41353Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41353 raw41353Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw41353 raw41353Labels = mixedMoment B raw41353step0 raw41353step0Labels := by
      have ha : raw41353step0 = (fun i j => raw41353 (permutation623 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41353step0 raw41353; decide +kernel
      have hl : raw41353step0Labels = raw41353Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41353 raw41353Labels permutation623 permutation6
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw41354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw41354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41354 raw41354Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw41354 raw41354Labels = mixedMoment B raw41354step0 raw41354step0Labels := by
      have ha : raw41354step0 = (fun i j => raw41354 (permutation541 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41354step0 raw41354; decide +kernel
      have hl : raw41354step0Labels = raw41354Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41354 raw41354Labels permutation541 permutation6
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw41355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw41355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw41355step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41355 raw41355Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw41355 raw41355Labels = mixedMoment B raw41355step0 raw41355step0Labels := by
      have hz : ∀ j, raw41355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41355step0 = (fun i j => raw41355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41355step0 raw41355; decide +kernel
      have hl : raw41355step0Labels = raw41355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41355 raw41355Labels permutation346 hz
    mixedMoment B raw41355step0 raw41355step0Labels = mixedMoment B raw41355step1 raw41355step1Labels := by
      have ha : raw41355step1 = (fun i j => raw41355step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41355step1 raw41355step0; decide +kernel
      have hl : raw41355step1Labels = raw41355step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41355step0 raw41355step0Labels permutation128 permutation6
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw41356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw41356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw41356step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41356 raw41356Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw41356 raw41356Labels = mixedMoment B raw41356step0 raw41356step0Labels := by
      have hz : ∀ j, raw41356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41356step0 = (fun i j => raw41356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41356step0 raw41356; decide +kernel
      have hl : raw41356step0Labels = raw41356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41356 raw41356Labels permutation346 hz
    mixedMoment B raw41356step0 raw41356step0Labels = mixedMoment B raw41356step1 raw41356step1Labels := by
      have ha : raw41356step1 = (fun i j => raw41356step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41356step1 raw41356step0; decide +kernel
      have hl : raw41356step1Labels = raw41356step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41356step0 raw41356step0Labels permutation104 permutation6
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw41357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw41357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw41357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41357 raw41357Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw41357 raw41357Labels = mixedMoment B raw41357step0 raw41357step0Labels := by
      have hz : ∀ j, raw41357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41357step0 = (fun i j => raw41357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41357step0 raw41357; decide +kernel
      have hl : raw41357step0Labels = raw41357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41357 raw41357Labels permutation346 hz
    mixedMoment B raw41357step0 raw41357step0Labels = mixedMoment B raw41357step1 raw41357step1Labels := by
      have ha : raw41357step1 = (fun i j => raw41357step0 (permutation108 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41357step1 raw41357step0; decide +kernel
      have hl : raw41357step1Labels = raw41357step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41357step0 raw41357step0Labels permutation108 permutation6
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw41358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]
def raw41358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41358 raw41358Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw41358 raw41358Labels = mixedMoment B raw41358step0 raw41358step0Labels := by
      have ha : raw41358step0 = (fun i j => raw41358 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41358step0 raw41358; decide +kernel
      have hl : raw41358step0Labels = raw41358Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41358 raw41358Labels permutation590 permutation6
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw41359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw41359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41359 raw41359Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw41359 raw41359Labels = mixedMoment B raw41359step0 raw41359step0Labels := by
      have ha : raw41359step0 = (fun i j => raw41359 (permutation526 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41359step0 raw41359; decide +kernel
      have hl : raw41359step0Labels = raw41359Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41359 raw41359Labels permutation526 permutation6
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw41360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw41360step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0]]
def raw41360step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41360step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw41360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41360 raw41360Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw41360 raw41360Labels = mixedMoment B raw41360step0 raw41360step0Labels := by
      have hz : ∀ j, raw41360 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41360step0 = (fun i j => raw41360 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41360step0 raw41360; decide +kernel
      have hl : raw41360step0Labels = raw41360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41360 raw41360Labels permutation520 hz
    mixedMoment B raw41360step0 raw41360step0Labels = mixedMoment B raw41360step1 raw41360step1Labels := by
      have hz : ∀ j, raw41360step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41360step1 = (fun i j => raw41360step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41360step1 raw41360step0; decide +kernel
      have hl : raw41360step1Labels = raw41360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41360step0 raw41360step0Labels permutation104 hz
    mixedMoment B raw41360step1 raw41360step1Labels = mixedMoment B raw41360step2 raw41360step2Labels := by
      have ha : raw41360step2 = (fun i j => raw41360step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41360step2 raw41360step1; decide +kernel
      have hl : raw41360step2Labels = raw41360step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41360step1 raw41360step1Labels permutation21 permutation6
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw41361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw41361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41361 raw41361Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw41361 raw41361Labels = mixedMoment B raw41361step0 raw41361step0Labels := by
      have hz : ∀ j, raw41361 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41361step0 = (fun i j => raw41361 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41361step0 raw41361; decide +kernel
      have hl : raw41361step0Labels = raw41361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41361 raw41361Labels permutation434 hz
    mixedMoment B raw41361step0 raw41361step0Labels = mixedMoment B raw41361step1 raw41361step1Labels := by
      have ha : raw41361step1 = (fun i j => raw41361step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41361step1 raw41361step0; decide +kernel
      have hl : raw41361step1Labels = raw41361step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41361step0 raw41361step0Labels permutation99 permutation6
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw41362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![2, 0, -2]]
def raw41362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41362 raw41362Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw41362 raw41362Labels = mixedMoment B raw41362step0 raw41362step0Labels := by
      have hz : ∀ j, raw41362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41362step0 = (fun i j => raw41362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41362step0 raw41362; decide +kernel
      have hl : raw41362step0Labels = raw41362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41362 raw41362Labels permutation434 hz
    mixedMoment B raw41362step0 raw41362step0Labels = mixedMoment B raw41362step1 raw41362step1Labels := by
      have ha : raw41362step1 = (fun i j => raw41362step0 (permutation111 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41362step1 raw41362step0; decide +kernel
      have hl : raw41362step1Labels = raw41362step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41362step0 raw41362step0Labels permutation111 permutation6
    mixedMoment B raw41362step1 raw41362step1Labels = mixedMoment B raw41362step2 raw41362step2Labels := by
      have ha : raw41362step2 = -raw41362step1 := by apply Matrix.ext; change ∀ i j, raw41362step2 i j = -(raw41362step1 i j); unfold raw41362step2 raw41362step1; decide +kernel
      have hl : raw41362step2Labels = raw41362step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw41363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41363 raw41363Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw41363 raw41363Labels = mixedMoment B raw41363step0 raw41363step0Labels := by
      have hz : ∀ j, raw41363 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41363step0 = (fun i j => raw41363 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41363step0 raw41363; decide +kernel
      have hl : raw41363step0Labels = raw41363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41363 raw41363Labels permutation434 hz
    mixedMoment B raw41363step0 raw41363step0Labels = mixedMoment B raw41363step1 raw41363step1Labels := by
      have ha : raw41363step1 = (fun i j => raw41363step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41363step1 raw41363step0; decide +kernel
      have hl : raw41363step1Labels = raw41363step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41363step0 raw41363step0Labels permutation93 permutation6
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw41364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw41364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41364 raw41364Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw41364 raw41364Labels = mixedMoment B raw41364step0 raw41364step0Labels := by
      have hz : ∀ j, raw41364 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41364step0 = (fun i j => raw41364 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41364step0 raw41364; decide +kernel
      have hl : raw41364step0Labels = raw41364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41364 raw41364Labels permutation434 hz
    mixedMoment B raw41364step0 raw41364step0Labels = mixedMoment B raw41364step1 raw41364step1Labels := by
      have ha : raw41364step1 = (fun i j => raw41364step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41364step1 raw41364step0; decide +kernel
      have hl : raw41364step1Labels = raw41364step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41364step0 raw41364step0Labels permutation83 permutation6
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw41365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41365 raw41365Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw41365 raw41365Labels = mixedMoment B raw41365step0 raw41365step0Labels := by
      have ha : raw41365step0 = (fun i j => raw41365 (permutation416 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41365step0 raw41365; decide +kernel
      have hl : raw41365step0Labels = raw41365Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41365 raw41365Labels permutation416 permutation6
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw41366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41366 raw41366Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw41366 raw41366Labels = mixedMoment B raw41366step0 raw41366step0Labels := by
      have ha : raw41366step0 = (fun i j => raw41366 (permutation402 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41366step0 raw41366; decide +kernel
      have hl : raw41366step0Labels = raw41366Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41366 raw41366Labels permutation402 permutation6
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw41367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw41367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41367 raw41367Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw41367 raw41367Labels = mixedMoment B raw41367step0 raw41367step0Labels := by
      have ha : raw41367step0 = (fun i j => raw41367 (permutation454 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41367step0 raw41367; decide +kernel
      have hl : raw41367step0Labels = raw41367Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41367 raw41367Labels permutation454 permutation6
    mixedMoment B raw41367step0 raw41367step0Labels = mixedMoment B raw41367step1 raw41367step1Labels := by
      have ha : raw41367step1 = -raw41367step0 := by apply Matrix.ext; change ∀ i j, raw41367step1 i j = -(raw41367step0 i j); unfold raw41367step1 raw41367step0; decide +kernel
      have hl : raw41367step1Labels = raw41367step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3689 node3689Labels := by rfl

def raw41368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw41368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw41368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw41368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw41368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41368 raw41368Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw41368 raw41368Labels = mixedMoment B raw41368step0 raw41368step0Labels := by
      have hz : ∀ j, raw41368 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41368step0 = (fun i j => raw41368 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41368step0 raw41368; decide +kernel
      have hl : raw41368step0Labels = raw41368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41368 raw41368Labels permutation520 hz
    mixedMoment B raw41368step0 raw41368step0Labels = mixedMoment B raw41368step1 raw41368step1Labels := by
      have ha : raw41368step1 = (fun i j => raw41368step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41368step1 raw41368step0; decide +kernel
      have hl : raw41368step1Labels = raw41368step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41368step0 raw41368step0Labels permutation145 permutation3
    mixedMoment B raw41368step1 raw41368step1Labels = mixedMoment B raw41368step2 raw41368step2Labels := by
      have ha : raw41368step2 = -raw41368step1 := by apply Matrix.ext; change ∀ i j, raw41368step2 i j = -(raw41368step1 i j); unfold raw41368step2 raw41368step1; decide +kernel
      have hl : raw41368step2Labels = raw41368step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw41369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw41369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41369 raw41369Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw41369 raw41369Labels = mixedMoment B raw41369step0 raw41369step0Labels := by
      have ha : raw41369step0 = (fun i j => raw41369 (permutation529 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41369step0 raw41369; decide +kernel
      have hl : raw41369step0Labels = raw41369Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41369 raw41369Labels permutation529 permutation6
    mixedMoment B raw41369step0 raw41369step0Labels = mixedMoment B raw41369step1 raw41369step1Labels := by
      have ha : raw41369step1 = -raw41369step0 := by apply Matrix.ext; change ∀ i j, raw41369step1 i j = -(raw41369step0 i j); unfold raw41369step1 raw41369step0; decide +kernel
      have hl : raw41369step1Labels = raw41369step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3692 node3692Labels := by rfl

def raw41370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![2, 1, -3]]
def raw41370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41370 raw41370Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw41370 raw41370Labels = mixedMoment B raw41370step0 raw41370step0Labels := by
      have hz : ∀ j, raw41370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41370step0 = (fun i j => raw41370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41370step0 raw41370; decide +kernel
      have hl : raw41370step0Labels = raw41370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41370 raw41370Labels permutation434 hz
    mixedMoment B raw41370step0 raw41370step0Labels = mixedMoment B raw41370step1 raw41370step1Labels := by
      have ha : raw41370step1 = (fun i j => raw41370step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41370step1 raw41370step0; decide +kernel
      have hl : raw41370step1Labels = raw41370step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41370step0 raw41370step0Labels permutation140 permutation6
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw41371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw41371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw41371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41371 raw41371Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw41371 raw41371Labels = mixedMoment B raw41371step0 raw41371step0Labels := by
      have hz : ∀ j, raw41371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41371step0 = (fun i j => raw41371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41371step0 raw41371; decide +kernel
      have hl : raw41371step0Labels = raw41371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41371 raw41371Labels permutation434 hz
    mixedMoment B raw41371step0 raw41371step0Labels = mixedMoment B raw41371step1 raw41371step1Labels := by
      have ha : raw41371step1 = (fun i j => raw41371step0 (permutation74 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41371step1 raw41371step0; decide +kernel
      have hl : raw41371step1Labels = raw41371step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41371step0 raw41371step0Labels permutation74 permutation6
    mixedMoment B raw41371step1 raw41371step1Labels = mixedMoment B raw41371step2 raw41371step2Labels := by
      have ha : raw41371step2 = -raw41371step1 := by apply Matrix.ext; change ∀ i j, raw41371step2 i j = -(raw41371step1 i j); unfold raw41371step2 raw41371step1; decide +kernel
      have hl : raw41371step2Labels = raw41371step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw41372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw41372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw41372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41372step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 2, -4]]
def raw41372step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41372step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41372 raw41372Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw41372 raw41372Labels = mixedMoment B raw41372step0 raw41372step0Labels := by
      have hz : ∀ j, raw41372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41372step0 = (fun i j => raw41372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41372step0 raw41372; decide +kernel
      have hl : raw41372step0Labels = raw41372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41372 raw41372Labels permutation434 hz
    mixedMoment B raw41372step0 raw41372step0Labels = mixedMoment B raw41372step1 raw41372step1Labels := by
      have hz : ∀ j, raw41372step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41372step1 = (fun i j => raw41372step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41372step1 raw41372step0; decide +kernel
      have hl : raw41372step1Labels = raw41372step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41372step0 raw41372step0Labels permutation80 hz
    mixedMoment B raw41372step1 raw41372step1Labels = mixedMoment B raw41372step2 raw41372step2Labels := by
      have ha : raw41372step2 = (fun i j => raw41372step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41372step2 raw41372step1; decide +kernel
      have hl : raw41372step2Labels = raw41372step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41372step1 raw41372step1Labels permutation26 permutation6
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw41373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw41373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw41373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 2, -3], ![1, -2, 1]]
def raw41373step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41373step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41373 raw41373Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw41373 raw41373Labels = mixedMoment B raw41373step0 raw41373step0Labels := by
      have hz : ∀ j, raw41373 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41373step0 = (fun i j => raw41373 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41373step0 raw41373; decide +kernel
      have hl : raw41373step0Labels = raw41373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41373 raw41373Labels permutation434 hz
    mixedMoment B raw41373step0 raw41373step0Labels = mixedMoment B raw41373step1 raw41373step1Labels := by
      have hz : ∀ j, raw41373step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41373step1 = (fun i j => raw41373step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41373step1 raw41373step0; decide +kernel
      have hl : raw41373step1Labels = raw41373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41373step0 raw41373step0Labels permutation80 hz
    mixedMoment B raw41373step1 raw41373step1Labels = mixedMoment B raw41373step2 raw41373step2Labels := by
      have ha : raw41373step2 = (fun i j => raw41373step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41373step2 raw41373step1; decide +kernel
      have hl : raw41373step2Labels = raw41373step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41373step1 raw41373step1Labels permutation21 permutation6
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw41374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]
def raw41374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]
def raw41374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41374 raw41374Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw41374 raw41374Labels = mixedMoment B raw41374step0 raw41374step0Labels := by
      have hz : ∀ j, raw41374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41374step0 = (fun i j => raw41374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41374step0 raw41374; decide +kernel
      have hl : raw41374step0Labels = raw41374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41374 raw41374Labels permutation346 hz
    mixedMoment B raw41374step0 raw41374step0Labels = mixedMoment B raw41374step1 raw41374step1Labels := by
      have ha : raw41374step1 = (fun i j => raw41374step0 (permutation131 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41374step1 raw41374step0; decide +kernel
      have hl : raw41374step1Labels = raw41374step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41374step0 raw41374step0Labels permutation131 permutation6
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw41375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw41375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw41375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41375 raw41375Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw41375 raw41375Labels = mixedMoment B raw41375step0 raw41375step0Labels := by
      have hz : ∀ j, raw41375 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41375step0 = (fun i j => raw41375 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41375step0 raw41375; decide +kernel
      have hl : raw41375step0Labels = raw41375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41375 raw41375Labels permutation346 hz
    mixedMoment B raw41375step0 raw41375step0Labels = mixedMoment B raw41375step1 raw41375step1Labels := by
      have ha : raw41375step1 = (fun i j => raw41375step0 (permutation109 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41375step1 raw41375step0; decide +kernel
      have hl : raw41375step1Labels = raw41375step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41375step0 raw41375step0Labels permutation109 permutation6
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw41376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw41376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw41376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41376 raw41376Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw41376 raw41376Labels = mixedMoment B raw41376step0 raw41376step0Labels := by
      have hz : ∀ j, raw41376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41376step0 = (fun i j => raw41376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41376step0 raw41376; decide +kernel
      have hl : raw41376step0Labels = raw41376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41376 raw41376Labels permutation346 hz
    mixedMoment B raw41376step0 raw41376step0Labels = mixedMoment B raw41376step1 raw41376step1Labels := by
      have ha : raw41376step1 = (fun i j => raw41376step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41376step1 raw41376step0; decide +kernel
      have hl : raw41376step1Labels = raw41376step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41376step0 raw41376step0Labels permutation122 permutation6
    _ = mixedMoment B node2561 node2561Labels := by rfl

def raw41377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41377 raw41377Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw41377 raw41377Labels = mixedMoment B raw41377step0 raw41377step0Labels := by
      have ha : raw41377step0 = (fun i j => raw41377 (permutation572 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41377step0 raw41377; decide +kernel
      have hl : raw41377step0Labels = raw41377Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41377 raw41377Labels permutation572 permutation6
    _ = mixedMoment B node2556 node2556Labels := by rfl

def raw41378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw41378step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![2, -1, -1]]
def raw41378step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41378step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw41378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41378step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41378step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41378 raw41378Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw41378 raw41378Labels = mixedMoment B raw41378step0 raw41378step0Labels := by
      have hz : ∀ j, raw41378 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41378step0 = (fun i j => raw41378 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41378step0 raw41378; decide +kernel
      have hl : raw41378step0Labels = raw41378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41378 raw41378Labels permutation520 hz
    mixedMoment B raw41378step0 raw41378step0Labels = mixedMoment B raw41378step1 raw41378step1Labels := by
      have hz : ∀ j, raw41378step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41378step1 = (fun i j => raw41378step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41378step1 raw41378step0; decide +kernel
      have hl : raw41378step1Labels = raw41378step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41378step0 raw41378step0Labels permutation104 hz
    mixedMoment B raw41378step1 raw41378step1Labels = mixedMoment B raw41378step2 raw41378step2Labels := by
      have ha : raw41378step2 = (fun i j => raw41378step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41378step2 raw41378step1; decide +kernel
      have hl : raw41378step2Labels = raw41378step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41378step1 raw41378step1Labels permutation15 permutation6
    mixedMoment B raw41378step2 raw41378step2Labels = mixedMoment B raw41378step3 raw41378step3Labels := by
      have ha : raw41378step3 = -raw41378step2 := by apply Matrix.ext; change ∀ i j, raw41378step3 i j = -(raw41378step2 i j); unfold raw41378step3 raw41378step2; decide +kernel
      have hl : raw41378step3Labels = raw41378step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw41379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2]]
def raw41379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41379step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41379 raw41379Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw41379 raw41379Labels = mixedMoment B raw41379step0 raw41379step0Labels := by
      have hz : ∀ j, raw41379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41379step0 = (fun i j => raw41379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41379step0 raw41379; decide +kernel
      have hl : raw41379step0Labels = raw41379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41379 raw41379Labels permutation434 hz
    mixedMoment B raw41379step0 raw41379step0Labels = mixedMoment B raw41379step1 raw41379step1Labels := by
      have ha : raw41379step1 = (fun i j => raw41379step0 (permutation69 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41379step1 raw41379step0; decide +kernel
      have hl : raw41379step1Labels = raw41379step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41379step0 raw41379step0Labels permutation69 permutation6
    mixedMoment B raw41379step1 raw41379step1Labels = mixedMoment B raw41379step2 raw41379step2Labels := by
      have ha : raw41379step2 = -raw41379step1 := by apply Matrix.ext; change ∀ i j, raw41379step2 i j = -(raw41379step1 i j); unfold raw41379step2 raw41379step1; decide +kernel
      have hl : raw41379step2Labels = raw41379step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw41380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41380step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41380 raw41380Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw41380 raw41380Labels = mixedMoment B raw41380step0 raw41380step0Labels := by
      have hz : ∀ j, raw41380 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41380step0 = (fun i j => raw41380 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41380step0 raw41380; decide +kernel
      have hl : raw41380step0Labels = raw41380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41380 raw41380Labels permutation434 hz
    mixedMoment B raw41380step0 raw41380step0Labels = mixedMoment B raw41380step1 raw41380step1Labels := by
      have ha : raw41380step1 = (fun i j => raw41380step0 (permutation75 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41380step1 raw41380step0; decide +kernel
      have hl : raw41380step1Labels = raw41380step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41380step0 raw41380step0Labels permutation75 permutation6
    mixedMoment B raw41380step1 raw41380step1Labels = mixedMoment B raw41380step2 raw41380step2Labels := by
      have ha : raw41380step2 = -raw41380step1 := by apply Matrix.ext; change ∀ i j, raw41380step2 i j = -(raw41380step1 i j); unfold raw41380step2 raw41380step1; decide +kernel
      have hl : raw41380step2Labels = raw41380step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw41381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41381 raw41381Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw41381 raw41381Labels = mixedMoment B raw41381step0 raw41381step0Labels := by
      have ha : raw41381step0 = (fun i j => raw41381 (permutation308 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41381step0 raw41381; decide +kernel
      have hl : raw41381step0Labels = raw41381Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41381 raw41381Labels permutation308 permutation6
    mixedMoment B raw41381step0 raw41381step0Labels = mixedMoment B raw41381step1 raw41381step1Labels := by
      have ha : raw41381step1 = -raw41381step0 := by apply Matrix.ext; change ∀ i j, raw41381step1 i j = -(raw41381step0 i j); unfold raw41381step1 raw41381step0; decide +kernel
      have hl : raw41381step1Labels = raw41381step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2479 node2479Labels := by rfl

def raw41382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw41382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw41382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41382 raw41382Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw41382 raw41382Labels = mixedMoment B raw41382step0 raw41382step0Labels := by
      have hz : ∀ j, raw41382 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41382step0 = (fun i j => raw41382 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41382step0 raw41382; decide +kernel
      have hl : raw41382step0Labels = raw41382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41382 raw41382Labels permutation520 hz
    mixedMoment B raw41382step0 raw41382step0Labels = mixedMoment B raw41382step1 raw41382step1Labels := by
      have ha : raw41382step1 = (fun i j => raw41382step0 (permutation60 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41382step1 raw41382step0; decide +kernel
      have hl : raw41382step1Labels = raw41382step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41382step0 raw41382step0Labels permutation60 permutation6
    mixedMoment B raw41382step1 raw41382step1Labels = mixedMoment B raw41382step2 raw41382step2Labels := by
      have ha : raw41382step2 = -raw41382step1 := by apply Matrix.ext; change ∀ i j, raw41382step2 i j = -(raw41382step1 i j); unfold raw41382step2 raw41382step1; decide +kernel
      have hl : raw41382step2Labels = raw41382step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw41383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw41383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41383 raw41383Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw41383 raw41383Labels = mixedMoment B raw41383step0 raw41383step0Labels := by
      have ha : raw41383step0 = (fun i j => raw41383 (permutation322 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41383step0 raw41383; decide +kernel
      have hl : raw41383step0Labels = raw41383Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41383 raw41383Labels permutation322 permutation6
    mixedMoment B raw41383step0 raw41383step0Labels = mixedMoment B raw41383step1 raw41383step1Labels := by
      have ha : raw41383step1 = -raw41383step0 := by apply Matrix.ext; change ∀ i j, raw41383step1 i j = -(raw41383step0 i j); unfold raw41383step1 raw41383step0; decide +kernel
      have hl : raw41383step1Labels = raw41383step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw41384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw41384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw41384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![2, 2, -4]]
def raw41384step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw41384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41384 raw41384Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw41384 raw41384Labels = mixedMoment B raw41384step0 raw41384step0Labels := by
      have hz : ∀ j, raw41384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41384step0 = (fun i j => raw41384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41384step0 raw41384; decide +kernel
      have hl : raw41384step0Labels = raw41384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41384 raw41384Labels permutation434 hz
    mixedMoment B raw41384step0 raw41384step0Labels = mixedMoment B raw41384step1 raw41384step1Labels := by
      have hz : ∀ j, raw41384step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41384step1 = (fun i j => raw41384step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41384step1 raw41384step0; decide +kernel
      have hl : raw41384step1Labels = raw41384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41384step0 raw41384step0Labels permutation80 hz
    mixedMoment B raw41384step1 raw41384step1Labels = mixedMoment B raw41384step2 raw41384step2Labels := by
      have ha : raw41384step2 = (fun i j => raw41384step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41384step2 raw41384step1; decide +kernel
      have hl : raw41384step2Labels = raw41384step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41384step1 raw41384step1Labels permutation27 permutation6
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw41385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw41385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw41385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![1, 2, -3], ![1, -1, 0]]
def raw41385step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41385step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw41385step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41385 raw41385Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw41385 raw41385Labels = mixedMoment B raw41385step0 raw41385step0Labels := by
      have hz : ∀ j, raw41385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41385step0 = (fun i j => raw41385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41385step0 raw41385; decide +kernel
      have hl : raw41385step0Labels = raw41385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41385 raw41385Labels permutation434 hz
    mixedMoment B raw41385step0 raw41385step0Labels = mixedMoment B raw41385step1 raw41385step1Labels := by
      have hz : ∀ j, raw41385step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41385step1 = (fun i j => raw41385step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41385step1 raw41385step0; decide +kernel
      have hl : raw41385step1Labels = raw41385step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41385step0 raw41385step0Labels permutation80 hz
    mixedMoment B raw41385step1 raw41385step1Labels = mixedMoment B raw41385step2 raw41385step2Labels := by
      have ha : raw41385step2 = (fun i j => raw41385step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41385step2 raw41385step1; decide +kernel
      have hl : raw41385step2Labels = raw41385step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41385step1 raw41385step1Labels permutation21 permutation6
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw41386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw41386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw41386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41386 raw41386Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw41386 raw41386Labels = mixedMoment B raw41386step0 raw41386step0Labels := by
      have hz : ∀ j, raw41386 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41386step0 = (fun i j => raw41386 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41386step0 raw41386; decide +kernel
      have hl : raw41386step0Labels = raw41386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41386 raw41386Labels permutation346 hz
    mixedMoment B raw41386step0 raw41386step0Labels = mixedMoment B raw41386step1 raw41386step1Labels := by
      have ha : raw41386step1 = (fun i j => raw41386step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41386step1 raw41386step0; decide +kernel
      have hl : raw41386step1Labels = raw41386step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41386step0 raw41386step0Labels permutation63 permutation6
    mixedMoment B raw41386step1 raw41386step1Labels = mixedMoment B raw41386step2 raw41386step2Labels := by
      have ha : raw41386step2 = -raw41386step1 := by apply Matrix.ext; change ∀ i j, raw41386step2 i j = -(raw41386step1 i j); unfold raw41386step2 raw41386step1; decide +kernel
      have hl : raw41386step2Labels = raw41386step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw41387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]
def raw41387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![2, 0, -2]]
def raw41387step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41387step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41387step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41387 raw41387Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw41387 raw41387Labels = mixedMoment B raw41387step0 raw41387step0Labels := by
      have hz : ∀ j, raw41387 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41387step0 = (fun i j => raw41387 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41387step0 raw41387; decide +kernel
      have hl : raw41387step0Labels = raw41387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41387 raw41387Labels permutation520 hz
    mixedMoment B raw41387step0 raw41387step0Labels = mixedMoment B raw41387step1 raw41387step1Labels := by
      have hz : ∀ j, raw41387step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41387step1 = (fun i j => raw41387step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41387step1 raw41387step0; decide +kernel
      have hl : raw41387step1Labels = raw41387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41387step0 raw41387step0Labels permutation104 hz
    mixedMoment B raw41387step1 raw41387step1Labels = mixedMoment B raw41387step2 raw41387step2Labels := by
      have ha : raw41387step2 = (fun i j => raw41387step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41387step2 raw41387step1; decide +kernel
      have hl : raw41387step2Labels = raw41387step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41387step1 raw41387step1Labels permutation15 permutation6
    mixedMoment B raw41387step2 raw41387step2Labels = mixedMoment B raw41387step3 raw41387step3Labels := by
      have ha : raw41387step3 = -raw41387step2 := by apply Matrix.ext; change ∀ i j, raw41387step3 i j = -(raw41387step2 i j); unfold raw41387step3 raw41387step2; decide +kernel
      have hl : raw41387step3Labels = raw41387step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw41388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw41388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw41388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41388 raw41388Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw41388 raw41388Labels = mixedMoment B raw41388step0 raw41388step0Labels := by
      have hz : ∀ j, raw41388 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41388step0 = (fun i j => raw41388 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41388step0 raw41388; decide +kernel
      have hl : raw41388step0Labels = raw41388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41388 raw41388Labels permutation520 hz
    mixedMoment B raw41388step0 raw41388step0Labels = mixedMoment B raw41388step1 raw41388step1Labels := by
      have ha : raw41388step1 = (fun i j => raw41388step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41388step1 raw41388step0; decide +kernel
      have hl : raw41388step1Labels = raw41388step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41388step0 raw41388step0Labels permutation56 permutation6
    mixedMoment B raw41388step1 raw41388step1Labels = mixedMoment B raw41388step2 raw41388step2Labels := by
      have ha : raw41388step2 = -raw41388step1 := by apply Matrix.ext; change ∀ i j, raw41388step2 i j = -(raw41388step1 i j); unfold raw41388step2 raw41388step1; decide +kernel
      have hl : raw41388step2Labels = raw41388step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw41389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]
def raw41389step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 1, -1], ![2, 1, -3]]
def raw41389step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41389step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41389step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41389step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41389 raw41389Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw41389 raw41389Labels = mixedMoment B raw41389step0 raw41389step0Labels := by
      have hz : ∀ j, raw41389 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41389step0 = (fun i j => raw41389 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41389step0 raw41389; decide +kernel
      have hl : raw41389step0Labels = raw41389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41389 raw41389Labels permutation520 hz
    mixedMoment B raw41389step0 raw41389step0Labels = mixedMoment B raw41389step1 raw41389step1Labels := by
      have hz : ∀ j, raw41389step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41389step1 = (fun i j => raw41389step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41389step1 raw41389step0; decide +kernel
      have hl : raw41389step1Labels = raw41389step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41389step0 raw41389step0Labels permutation104 hz
    mixedMoment B raw41389step1 raw41389step1Labels = mixedMoment B raw41389step2 raw41389step2Labels := by
      have ha : raw41389step2 = (fun i j => raw41389step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41389step2 raw41389step1; decide +kernel
      have hl : raw41389step2Labels = raw41389step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41389step1 raw41389step1Labels permutation14 permutation6
    mixedMoment B raw41389step2 raw41389step2Labels = mixedMoment B raw41389step3 raw41389step3Labels := by
      have ha : raw41389step3 = -raw41389step2 := by apply Matrix.ext; change ∀ i j, raw41389step3 i j = -(raw41389step2 i j); unfold raw41389step3 raw41389step2; decide +kernel
      have hl : raw41389step3Labels = raw41389step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw41390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw41390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw41390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 0, 0], ![2, 2, -4]]
def raw41390step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41390step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![2, 2, -4]]
def raw41390step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41390step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw41390step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41390step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw41390step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41390 raw41390Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw41390 raw41390Labels = mixedMoment B raw41390step0 raw41390step0Labels := by
      have hz : ∀ j, raw41390 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41390step0 = (fun i j => raw41390 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41390step0 raw41390; decide +kernel
      have hl : raw41390step0Labels = raw41390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41390 raw41390Labels permutation520 hz
    mixedMoment B raw41390step0 raw41390step0Labels = mixedMoment B raw41390step1 raw41390step1Labels := by
      have hz : ∀ j, raw41390step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41390step1 = (fun i j => raw41390step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41390step1 raw41390step0; decide +kernel
      have hl : raw41390step1Labels = raw41390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41390step0 raw41390step0Labels permutation104 hz
    mixedMoment B raw41390step1 raw41390step1Labels = mixedMoment B raw41390step2 raw41390step2Labels := by
      have hz : ∀ j, raw41390step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41390step2 = (fun i j => raw41390step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41390step2 raw41390step1; decide +kernel
      have hl : raw41390step2Labels = raw41390step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41390step1 raw41390step1Labels permutation20 hz
    mixedMoment B raw41390step2 raw41390step2Labels = mixedMoment B raw41390step3 raw41390step3Labels := by
      have ha : raw41390step3 = (fun i j => raw41390step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41390step3 raw41390step2; decide +kernel
      have hl : raw41390step3Labels = raw41390step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41390step2 raw41390step2Labels permutation4 permutation6
    mixedMoment B raw41390step3 raw41390step3Labels = mixedMoment B raw41390step4 raw41390step4Labels := by
      have ha : raw41390step4 = -raw41390step3 := by apply Matrix.ext; change ∀ i j, raw41390step4 i j = -(raw41390step3 i j); unfold raw41390step4 raw41390step3; decide +kernel
      have hl : raw41390step4Labels = raw41390step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw41391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![3, -2, -1]]
def raw41391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41391 raw41391Labels = mixedMoment B node2131 node2131Labels := by
  calc
    mixedMoment B raw41391 raw41391Labels = mixedMoment B raw41391step0 raw41391step0Labels := by
      have ha : raw41391step0 = (fun i j => raw41391 (permutation505 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41391step0 raw41391; decide +kernel
      have hl : raw41391step0Labels = raw41391Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41391 raw41391Labels permutation505 permutation6
    _ = mixedMoment B node2131 node2131Labels := by rfl

def raw41392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![3, -1, -2]]
def raw41392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41392 raw41392Labels = mixedMoment B node1821 node1821Labels := by
  calc
    mixedMoment B raw41392 raw41392Labels = mixedMoment B raw41392step0 raw41392step0Labels := by
      have ha : raw41392step0 = (fun i j => raw41392 (permutation505 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41392step0 raw41392; decide +kernel
      have hl : raw41392step0Labels = raw41392Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41392 raw41392Labels permutation505 permutation6
    _ = mixedMoment B node1821 node1821Labels := by rfl

def raw41393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw41393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41393 raw41393Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw41393 raw41393Labels = mixedMoment B raw41393step0 raw41393step0Labels := by
      have ha : raw41393step0 = (fun i j => raw41393 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41393step0 raw41393; decide +kernel
      have hl : raw41393step0Labels = raw41393Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41393 raw41393Labels permutation499 permutation6
    _ = mixedMoment B node2252 node2252Labels := by rfl

def raw41394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw41394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41394 raw41394Labels = mixedMoment B node2104 node2104Labels := by
  calc
    mixedMoment B raw41394 raw41394Labels = mixedMoment B raw41394step0 raw41394step0Labels := by
      have ha : raw41394step0 = (fun i j => raw41394 (permutation505 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41394step0 raw41394; decide +kernel
      have hl : raw41394step0Labels = raw41394Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41394 raw41394Labels permutation505 permutation6
    _ = mixedMoment B node2104 node2104Labels := by rfl

def raw41395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw41395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw41395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41395 raw41395Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw41395 raw41395Labels = mixedMoment B raw41395step0 raw41395step0Labels := by
      have ha : raw41395step0 = (fun i j => raw41395 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41395step0 raw41395; decide +kernel
      have hl : raw41395step0Labels = raw41395Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41395 raw41395Labels permutation683 permutation3
    mixedMoment B raw41395step0 raw41395step0Labels = mixedMoment B raw41395step1 raw41395step1Labels := by
      have ha : raw41395step1 = -raw41395step0 := by apply Matrix.ext; change ∀ i j, raw41395step1 i j = -(raw41395step0 i j); unfold raw41395step1 raw41395step0; decide +kernel
      have hl : raw41395step1Labels = raw41395step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2252 node2252Labels := by rfl

def raw41396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw41396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41396 raw41396Labels = mixedMoment B node2806 node2806Labels := by
  calc
    mixedMoment B raw41396 raw41396Labels = mixedMoment B raw41396step0 raw41396step0Labels := by
      have ha : raw41396step0 = (fun i j => raw41396 (permutation647 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41396step0 raw41396; decide +kernel
      have hl : raw41396step0Labels = raw41396Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41396 raw41396Labels permutation647 permutation6
    _ = mixedMoment B node2806 node2806Labels := by rfl

def raw41397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw41397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41397 raw41397Labels = mixedMoment B node1125 node1125Labels := by
  calc
    mixedMoment B raw41397 raw41397Labels = mixedMoment B raw41397step0 raw41397step0Labels := by
      have ha : raw41397step0 = (fun i j => raw41397 (permutation647 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41397step0 raw41397; decide +kernel
      have hl : raw41397step0Labels = raw41397Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41397 raw41397Labels permutation647 permutation6
    _ = mixedMoment B node1125 node1125Labels := by rfl

def raw41398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw41398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41398 raw41398Labels = mixedMoment B node597 node597Labels := by
  calc
    mixedMoment B raw41398 raw41398Labels = mixedMoment B raw41398step0 raw41398step0Labels := by
      have ha : raw41398step0 = (fun i j => raw41398 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41398step0 raw41398; decide +kernel
      have hl : raw41398step0Labels = raw41398Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41398 raw41398Labels permutation590 permutation6
    _ = mixedMoment B node597 node597Labels := by rfl

def raw41399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41399 raw41399Labels = mixedMoment B node577 node577Labels := by
  calc
    mixedMoment B raw41399 raw41399Labels = mixedMoment B raw41399step0 raw41399step0Labels := by
      have ha : raw41399step0 = (fun i j => raw41399 (permutation665 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41399step0 raw41399; decide +kernel
      have hl : raw41399step0Labels = raw41399Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41399 raw41399Labels permutation665 permutation6
    _ = mixedMoment B node577 node577Labels := by rfl

def raw41400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![3, -2, -1]]
def raw41400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![3, -2, -1]]
def raw41400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41400 raw41400Labels = mixedMoment B node2132 node2132Labels := by
  calc
    mixedMoment B raw41400 raw41400Labels = mixedMoment B raw41400step0 raw41400step0Labels := by
      have hz : ∀ j, raw41400 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41400step0 = (fun i j => raw41400 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41400step0 raw41400; decide +kernel
      have hl : raw41400step0Labels = raw41400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41400 raw41400Labels permutation520 hz
    mixedMoment B raw41400step0 raw41400step0Labels = mixedMoment B raw41400step1 raw41400step1Labels := by
      have ha : raw41400step1 = (fun i j => raw41400step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41400step1 raw41400step0; decide +kernel
      have hl : raw41400step1Labels = raw41400step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41400step0 raw41400step0Labels permutation122 permutation6
    _ = mixedMoment B node2132 node2132Labels := by rfl

def raw41401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![3, -1, -2]]
def raw41401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41401 raw41401Labels = mixedMoment B node1822 node1822Labels := by
  calc
    mixedMoment B raw41401 raw41401Labels = mixedMoment B raw41401step0 raw41401step0Labels := by
      have ha : raw41401step0 = (fun i j => raw41401 (permutation506 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41401step0 raw41401; decide +kernel
      have hl : raw41401step0Labels = raw41401Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41401 raw41401Labels permutation506 permutation6
    _ = mixedMoment B node1822 node1822Labels := by rfl

def raw41402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41402 raw41402Labels = mixedMoment B node2088 node2088Labels := by
  calc
    mixedMoment B raw41402 raw41402Labels = mixedMoment B raw41402step0 raw41402step0Labels := by
      have ha : raw41402step0 = (fun i j => raw41402 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41402step0 raw41402; decide +kernel
      have hl : raw41402step0Labels = raw41402Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41402 raw41402Labels permutation514 permutation6
    _ = mixedMoment B node2088 node2088Labels := by rfl

def raw41403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw41403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41403 raw41403Labels = mixedMoment B node1803 node1803Labels := by
  calc
    mixedMoment B raw41403 raw41403Labels = mixedMoment B raw41403step0 raw41403step0Labels := by
      have ha : raw41403step0 = (fun i j => raw41403 (permutation506 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41403step0 raw41403; decide +kernel
      have hl : raw41403step0Labels = raw41403Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41403 raw41403Labels permutation506 permutation6
    _ = mixedMoment B node1803 node1803Labels := by rfl

def raw41404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw41404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41404 raw41404Labels = mixedMoment B node601 node601Labels := by
  calc
    mixedMoment B raw41404 raw41404Labels = mixedMoment B raw41404step0 raw41404step0Labels := by
      have hz : ∀ j, raw41404 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41404step0 = (fun i j => raw41404 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41404step0 raw41404; decide +kernel
      have hl : raw41404step0Labels = raw41404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41404 raw41404Labels permutation434 hz
    mixedMoment B raw41404step0 raw41404step0Labels = mixedMoment B raw41404step1 raw41404step1Labels := by
      have ha : raw41404step1 = (fun i j => raw41404step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41404step1 raw41404step0; decide +kernel
      have hl : raw41404step1Labels = raw41404step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41404step0 raw41404step0Labels permutation129 permutation6
    _ = mixedMoment B node601 node601Labels := by rfl

def raw41405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41405 raw41405Labels = mixedMoment B node578 node578Labels := by
  calc
    mixedMoment B raw41405 raw41405Labels = mixedMoment B raw41405step0 raw41405step0Labels := by
      have ha : raw41405step0 = (fun i j => raw41405 (permutation666 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41405step0 raw41405; decide +kernel
      have hl : raw41405step0Labels = raw41405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41405 raw41405Labels permutation666 permutation6
    _ = mixedMoment B node578 node578Labels := by rfl

def raw41406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![3, -1, -2]]
def raw41406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![3, -1, -2]]
def raw41406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41406 raw41406Labels = mixedMoment B node1823 node1823Labels := by
  calc
    mixedMoment B raw41406 raw41406Labels = mixedMoment B raw41406step0 raw41406step0Labels := by
      have hz : ∀ j, raw41406 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41406step0 = (fun i j => raw41406 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41406step0 raw41406; decide +kernel
      have hl : raw41406step0Labels = raw41406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41406 raw41406Labels permutation520 hz
    mixedMoment B raw41406step0 raw41406step0Labels = mixedMoment B raw41406step1 raw41406step1Labels := by
      have ha : raw41406step1 = (fun i j => raw41406step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41406step1 raw41406step0; decide +kernel
      have hl : raw41406step1Labels = raw41406step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41406step0 raw41406step0Labels permutation122 permutation6
    _ = mixedMoment B node1823 node1823Labels := by rfl

def raw41407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41407 raw41407Labels = mixedMoment B node1789 node1789Labels := by
  calc
    mixedMoment B raw41407 raw41407Labels = mixedMoment B raw41407step0 raw41407step0Labels := by
      have ha : raw41407step0 = (fun i j => raw41407 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41407step0 raw41407; decide +kernel
      have hl : raw41407step0Labels = raw41407Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41407 raw41407Labels permutation514 permutation6
    _ = mixedMoment B node1789 node1789Labels := by rfl

def raw41408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![3, -1, -2]]
def raw41408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw41408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41408 raw41408Labels = mixedMoment B node2529 node2529Labels := by
  calc
    mixedMoment B raw41408 raw41408Labels = mixedMoment B raw41408step0 raw41408step0Labels := by
      have ha : raw41408step0 = (fun i j => raw41408 (permutation349 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41408step0 raw41408; decide +kernel
      have hl : raw41408step0Labels = raw41408Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41408 raw41408Labels permutation349 permutation6
    mixedMoment B raw41408step0 raw41408step0Labels = mixedMoment B raw41408step1 raw41408step1Labels := by
      have ha : raw41408step1 = -raw41408step0 := by apply Matrix.ext; change ∀ i j, raw41408step1 i j = -(raw41408step0 i j); unfold raw41408step1 raw41408step0; decide +kernel
      have hl : raw41408step1Labels = raw41408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2529 node2529Labels := by rfl

def raw41409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw41409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41409step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41409 raw41409Labels = mixedMoment B node2524 node2524Labels := by
  calc
    mixedMoment B raw41409 raw41409Labels = mixedMoment B raw41409step0 raw41409step0Labels := by
      have ha : raw41409step0 = (fun i j => raw41409 (permutation348 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41409step0 raw41409; decide +kernel
      have hl : raw41409step0Labels = raw41409Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41409 raw41409Labels permutation348 permutation6
    mixedMoment B raw41409step0 raw41409step0Labels = mixedMoment B raw41409step1 raw41409step1Labels := by
      have ha : raw41409step1 = -raw41409step0 := by apply Matrix.ext; change ∀ i j, raw41409step1 i j = -(raw41409step0 i j); unfold raw41409step1 raw41409step0; decide +kernel
      have hl : raw41409step1Labels = raw41409step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2524 node2524Labels := by rfl

def raw41410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41410 raw41410Labels = mixedMoment B node1111 node1111Labels := by
  calc
    mixedMoment B raw41410 raw41410Labels = mixedMoment B raw41410step0 raw41410step0Labels := by
      have ha : raw41410step0 = (fun i j => raw41410 (permutation659 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41410step0 raw41410; decide +kernel
      have hl : raw41410step0Labels = raw41410Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41410 raw41410Labels permutation659 permutation6
    _ = mixedMoment B node1111 node1111Labels := by rfl

def raw41411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw41411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41411 raw41411Labels = mixedMoment B node579 node579Labels := by
  calc
    mixedMoment B raw41411 raw41411Labels = mixedMoment B raw41411step0 raw41411step0Labels := by
      have hz : ∀ j, raw41411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41411step0 = (fun i j => raw41411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41411step0 raw41411; decide +kernel
      have hl : raw41411step0Labels = raw41411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41411 raw41411Labels permutation434 hz
    mixedMoment B raw41411step0 raw41411step0Labels = mixedMoment B raw41411step1 raw41411step1Labels := by
      have ha : raw41411step1 = (fun i j => raw41411step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41411step1 raw41411step0; decide +kernel
      have hl : raw41411step1Labels = raw41411step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41411step0 raw41411step0Labels permutation146 permutation6
    _ = mixedMoment B node579 node579Labels := by rfl

def raw41412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41412 raw41412Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw41412 raw41412Labels = mixedMoment B raw41412step0 raw41412step0Labels := by
      have ha : raw41412step0 = (fun i j => raw41412 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41412step0 raw41412; decide +kernel
      have hl : raw41412step0Labels = raw41412Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41412 raw41412Labels permutation414 permutation6
    _ = mixedMoment B node2105 node2105Labels := by rfl

def raw41413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41413 raw41413Labels = mixedMoment B node1802 node1802Labels := by
  calc
    mixedMoment B raw41413 raw41413Labels = mixedMoment B raw41413step0 raw41413step0Labels := by
      have ha : raw41413step0 = (fun i j => raw41413 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41413step0 raw41413; decide +kernel
      have hl : raw41413step0Labels = raw41413Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41413 raw41413Labels permutation414 permutation6
    _ = mixedMoment B node1802 node1802Labels := by rfl

def raw41414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41414 raw41414Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw41414 raw41414Labels = mixedMoment B raw41414step0 raw41414step0Labels := by
      have ha : raw41414step0 = (fun i j => raw41414 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41414step0 raw41414; decide +kernel
      have hl : raw41414step0Labels = raw41414Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41414 raw41414Labels permutation399 permutation6
    _ = mixedMoment B node2051 node2051Labels := by rfl

def raw41415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41415 raw41415Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw41415 raw41415Labels = mixedMoment B raw41415step0 raw41415step0Labels := by
      have ha : raw41415step0 = (fun i j => raw41415 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41415step0 raw41415; decide +kernel
      have hl : raw41415step0Labels = raw41415Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41415 raw41415Labels permutation409 permutation6
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw41416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41416 raw41416Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw41416 raw41416Labels = mixedMoment B raw41416step0 raw41416step0Labels := by
      have ha : raw41416step0 = (fun i j => raw41416 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41416step0 raw41416; decide +kernel
      have hl : raw41416step0Labels = raw41416Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41416 raw41416Labels permutation409 permutation6
    _ = mixedMoment B node2019 node2019Labels := by rfl

def raw41417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw41417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41417 raw41417Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw41417 raw41417Labels = mixedMoment B raw41417step0 raw41417step0Labels := by
      have ha : raw41417step0 = (fun i j => raw41417 (permutation395 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41417step0 raw41417; decide +kernel
      have hl : raw41417step0Labels = raw41417Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41417 raw41417Labels permutation395 permutation6
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw41418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1]]
def raw41418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41418 raw41418Labels = mixedMoment B node3786 node3786Labels := by
  calc
    mixedMoment B raw41418 raw41418Labels = mixedMoment B raw41418step0 raw41418step0Labels := by
      have ha : raw41418step0 = (fun i j => raw41418 (permutation395 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41418step0 raw41418; decide +kernel
      have hl : raw41418step0Labels = raw41418Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41418 raw41418Labels permutation395 permutation6
    _ = mixedMoment B node3786 node3786Labels := by rfl

def raw41419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw41419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41419 raw41419Labels = mixedMoment B node1966 node1966Labels := by
  calc
    mixedMoment B raw41419 raw41419Labels = mixedMoment B raw41419step0 raw41419step0Labels := by
      have ha : raw41419step0 = (fun i j => raw41419 (permutation523 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41419step0 raw41419; decide +kernel
      have hl : raw41419step0Labels = raw41419Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41419 raw41419Labels permutation523 permutation6
    mixedMoment B raw41419step0 raw41419step0Labels = mixedMoment B raw41419step1 raw41419step1Labels := by
      have ha : raw41419step1 = -raw41419step0 := by apply Matrix.ext; change ∀ i j, raw41419step1 i j = -(raw41419step0 i j); unfold raw41419step1 raw41419step0; decide +kernel
      have hl : raw41419step1Labels = raw41419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1966 node1966Labels := by rfl

def raw41420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41420 raw41420Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw41420 raw41420Labels = mixedMoment B raw41420step0 raw41420step0Labels := by
      have ha : raw41420step0 = (fun i j => raw41420 (permutation594 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41420step0 raw41420; decide +kernel
      have hl : raw41420step0Labels = raw41420Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41420 raw41420Labels permutation594 permutation6
    mixedMoment B raw41420step0 raw41420step0Labels = mixedMoment B raw41420step1 raw41420step1Labels := by
      have ha : raw41420step1 = -raw41420step0 := by apply Matrix.ext; change ∀ i j, raw41420step1 i j = -(raw41420step0 i j); unfold raw41420step1 raw41420step0; decide +kernel
      have hl : raw41420step1Labels = raw41420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3493 node3493Labels := by rfl

def raw41421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41421 raw41421Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw41421 raw41421Labels = mixedMoment B raw41421step0 raw41421step0Labels := by
      have ha : raw41421step0 = (fun i j => raw41421 (permutation389 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41421step0 raw41421; decide +kernel
      have hl : raw41421step0Labels = raw41421Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41421 raw41421Labels permutation389 permutation6
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw41422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw41422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41422 raw41422Labels = mixedMoment B node2807 node2807Labels := by
  calc
    mixedMoment B raw41422 raw41422Labels = mixedMoment B raw41422step0 raw41422step0Labels := by
      have ha : raw41422step0 = (fun i j => raw41422 (permutation623 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41422step0 raw41422; decide +kernel
      have hl : raw41422step0Labels = raw41422Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41422 raw41422Labels permutation623 permutation6
    _ = mixedMoment B node2807 node2807Labels := by rfl

def raw41423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw41423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41423 raw41423Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw41423 raw41423Labels = mixedMoment B raw41423step0 raw41423step0Labels := by
      have ha : raw41423step0 = (fun i j => raw41423 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41423step0 raw41423; decide +kernel
      have hl : raw41423step0Labels = raw41423Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41423 raw41423Labels permutation399 permutation6
    _ = mixedMoment B node3703 node3703Labels := by rfl

def raw41424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw41424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41424 raw41424Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw41424 raw41424Labels = mixedMoment B raw41424step0 raw41424step0Labels := by
      have ha : raw41424step0 = (fun i j => raw41424 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41424step0 raw41424; decide +kernel
      have hl : raw41424step0Labels = raw41424Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41424 raw41424Labels permutation409 permutation6
    _ = mixedMoment B node3689 node3689Labels := by rfl

def raw41425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw41425Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41425step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41425 raw41425Labels = mixedMoment B node1964 node1964Labels := by
  calc
    mixedMoment B raw41425 raw41425Labels = mixedMoment B raw41425step0 raw41425step0Labels := by
      have ha : raw41425step0 = (fun i j => raw41425 (permutation520 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41425step0 raw41425; decide +kernel
      have hl : raw41425step0Labels = raw41425Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41425 raw41425Labels permutation520 permutation6
    mixedMoment B raw41425step0 raw41425step0Labels = mixedMoment B raw41425step1 raw41425step1Labels := by
      have ha : raw41425step1 = -raw41425step0 := by apply Matrix.ext; change ∀ i j, raw41425step1 i j = -(raw41425step0 i j); unfold raw41425step1 raw41425step0; decide +kernel
      have hl : raw41425step1Labels = raw41425step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1964 node1964Labels := by rfl

def raw41426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -3, 2]]
def raw41426Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41426 raw41426Labels = mixedMoment B node3496 node3496Labels := by
  calc
    mixedMoment B raw41426 raw41426Labels = mixedMoment B raw41426step0 raw41426step0Labels := by
      have ha : raw41426step0 = (fun i j => raw41426 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41426step0 raw41426; decide +kernel
      have hl : raw41426step0Labels = raw41426Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41426 raw41426Labels permutation590 permutation6
    mixedMoment B raw41426step0 raw41426step0Labels = mixedMoment B raw41426step1 raw41426step1Labels := by
      have ha : raw41426step1 = -raw41426step0 := by apply Matrix.ext; change ∀ i j, raw41426step1 i j = -(raw41426step0 i j); unfold raw41426step1 raw41426step0; decide +kernel
      have hl : raw41426step1Labels = raw41426step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3496 node3496Labels := by rfl

def raw41427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw41427Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41427 raw41427Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw41427 raw41427Labels = mixedMoment B raw41427step0 raw41427step0Labels := by
      have ha : raw41427step0 = (fun i j => raw41427 (permutation623 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41427step0 raw41427; decide +kernel
      have hl : raw41427step0Labels = raw41427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41427 raw41427Labels permutation623 permutation6
    _ = mixedMoment B node1126 node1126Labels := by rfl

def raw41428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw41428Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41428 raw41428Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw41428 raw41428Labels = mixedMoment B raw41428step0 raw41428step0Labels := by
      have ha : raw41428step0 = (fun i j => raw41428 (permutation541 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41428step0 raw41428; decide +kernel
      have hl : raw41428step0Labels = raw41428Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41428 raw41428Labels permutation541 permutation6
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw41429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw41429Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41429 raw41429Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw41429 raw41429Labels = mixedMoment B raw41429step0 raw41429step0Labels := by
      have ha : raw41429step0 = (fun i j => raw41429 (permutation547 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41429step0 raw41429; decide +kernel
      have hl : raw41429step0Labels = raw41429Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41429 raw41429Labels permutation547 permutation6
    _ = mixedMoment B node2479 node2479Labels := by rfl

def raw41430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw41430Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41430 raw41430Labels = mixedMoment B node599 node599Labels := by
  calc
    mixedMoment B raw41430 raw41430Labels = mixedMoment B raw41430step0 raw41430step0Labels := by
      have ha : raw41430step0 = (fun i j => raw41430 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41430step0 raw41430; decide +kernel
      have hl : raw41430step0Labels = raw41430Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41430 raw41430Labels permutation590 permutation6
    _ = mixedMoment B node599 node599Labels := by rfl

def raw41431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw41431Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41431 raw41431Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw41431 raw41431Labels = mixedMoment B raw41431step0 raw41431step0Labels := by
      have ha : raw41431step0 = (fun i j => raw41431 (permutation569 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41431step0 raw41431; decide +kernel
      have hl : raw41431step0Labels = raw41431Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41431 raw41431Labels permutation569 permutation6
    _ = mixedMoment B node1039 node1039Labels := by rfl

def raw41432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![3, -1, -2]]
def raw41432Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![3, -1, -2]]
def raw41432step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41432 raw41432Labels = mixedMoment B node1827 node1827Labels := by
  calc
    mixedMoment B raw41432 raw41432Labels = mixedMoment B raw41432step0 raw41432step0Labels := by
      have hz : ∀ j, raw41432 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41432step0 = (fun i j => raw41432 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41432step0 raw41432; decide +kernel
      have hl : raw41432step0Labels = raw41432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41432 raw41432Labels permutation520 hz
    mixedMoment B raw41432step0 raw41432step0Labels = mixedMoment B raw41432step1 raw41432step1Labels := by
      have ha : raw41432step1 = (fun i j => raw41432step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41432step1 raw41432step0; decide +kernel
      have hl : raw41432step1Labels = raw41432step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41432step0 raw41432step0Labels permutation122 permutation6
    _ = mixedMoment B node1827 node1827Labels := by rfl

def raw41433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41433Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41433 raw41433Labels = mixedMoment B node1792 node1792Labels := by
  calc
    mixedMoment B raw41433 raw41433Labels = mixedMoment B raw41433step0 raw41433step0Labels := by
      have ha : raw41433step0 = (fun i j => raw41433 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41433step0 raw41433; decide +kernel
      have hl : raw41433step0Labels = raw41433Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41433 raw41433Labels permutation514 permutation6
    _ = mixedMoment B node1792 node1792Labels := by rfl

def raw41434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41434Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw41434step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41434 raw41434Labels = mixedMoment B node583 node583Labels := by
  calc
    mixedMoment B raw41434 raw41434Labels = mixedMoment B raw41434step0 raw41434step0Labels := by
      have hz : ∀ j, raw41434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41434step0 = (fun i j => raw41434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41434step0 raw41434; decide +kernel
      have hl : raw41434step0Labels = raw41434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41434 raw41434Labels permutation434 hz
    mixedMoment B raw41434step0 raw41434step0Labels = mixedMoment B raw41434step1 raw41434step1Labels := by
      have ha : raw41434step1 = (fun i j => raw41434step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41434step1 raw41434step0; decide +kernel
      have hl : raw41434step1Labels = raw41434step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41434step0 raw41434step0Labels permutation146 permutation6
    _ = mixedMoment B node583 node583Labels := by rfl

def raw41435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41435Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![2, -2, 0]]
def raw41435step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![2, -2, 0]]
def raw41435step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41435step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41435 raw41435Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw41435 raw41435Labels = mixedMoment B raw41435step0 raw41435step0Labels := by
      have hz : ∀ j, raw41435 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41435step0 = (fun i j => raw41435 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41435step0 raw41435; decide +kernel
      have hl : raw41435step0Labels = raw41435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41435 raw41435Labels permutation520 hz
    mixedMoment B raw41435step0 raw41435step0Labels = mixedMoment B raw41435step1 raw41435step1Labels := by
      have hz : ∀ j, raw41435step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41435step1 = (fun i j => raw41435step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41435step1 raw41435step0; decide +kernel
      have hl : raw41435step1Labels = raw41435step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41435step0 raw41435step0Labels permutation104 hz
    mixedMoment B raw41435step1 raw41435step1Labels = mixedMoment B raw41435step2 raw41435step2Labels := by
      have ha : raw41435step2 = (fun i j => raw41435step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41435step2 raw41435step1; decide +kernel
      have hl : raw41435step2Labels = raw41435step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41435step1 raw41435step1Labels permutation24 permutation6
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw41436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41436Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![2, -1, -1]]
def raw41436step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41436 raw41436Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw41436 raw41436Labels = mixedMoment B raw41436step0 raw41436step0Labels := by
      have hz : ∀ j, raw41436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41436step0 = (fun i j => raw41436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41436step0 raw41436; decide +kernel
      have hl : raw41436step0Labels = raw41436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41436 raw41436Labels permutation434 hz
    mixedMoment B raw41436step0 raw41436step0Labels = mixedMoment B raw41436step1 raw41436step1Labels := by
      have ha : raw41436step1 = (fun i j => raw41436step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41436step1 raw41436step0; decide +kernel
      have hl : raw41436step1Labels = raw41436step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41436step0 raw41436step0Labels permutation99 permutation6
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw41437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41437Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -2, 2], ![2, 0, -2]]
def raw41437step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41437 raw41437Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw41437 raw41437Labels = mixedMoment B raw41437step0 raw41437step0Labels := by
      have hz : ∀ j, raw41437 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41437step0 = (fun i j => raw41437 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41437step0 raw41437; decide +kernel
      have hl : raw41437step0Labels = raw41437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41437 raw41437Labels permutation434 hz
    mixedMoment B raw41437step0 raw41437step0Labels = mixedMoment B raw41437step1 raw41437step1Labels := by
      have ha : raw41437step1 = (fun i j => raw41437step0 (permutation98 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41437step1 raw41437step0; decide +kernel
      have hl : raw41437step1Labels = raw41437step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41437step0 raw41437step0Labels permutation98 permutation6
    _ = mixedMoment B node1810 node1810Labels := by rfl

def raw41438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41438Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41438step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41438 raw41438Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw41438 raw41438Labels = mixedMoment B raw41438step0 raw41438step0Labels := by
      have hz : ∀ j, raw41438 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41438step0 = (fun i j => raw41438 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41438step0 raw41438; decide +kernel
      have hl : raw41438step0Labels = raw41438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41438 raw41438Labels permutation434 hz
    mixedMoment B raw41438step0 raw41438step0Labels = mixedMoment B raw41438step1 raw41438step1Labels := by
      have ha : raw41438step1 = (fun i j => raw41438step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41438step1 raw41438step0; decide +kernel
      have hl : raw41438step1Labels = raw41438step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41438step0 raw41438step0Labels permutation93 permutation6
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw41439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41439step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41439 raw41439Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw41439 raw41439Labels = mixedMoment B raw41439step0 raw41439step0Labels := by
      have hz : ∀ j, raw41439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41439step0 = (fun i j => raw41439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41439step0 raw41439; decide +kernel
      have hl : raw41439step0Labels = raw41439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41439 raw41439Labels permutation434 hz
    mixedMoment B raw41439step0 raw41439step0Labels = mixedMoment B raw41439step1 raw41439step1Labels := by
      have ha : raw41439step1 = (fun i j => raw41439step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41439step1 raw41439step0; decide +kernel
      have hl : raw41439step1Labels = raw41439step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41439step0 raw41439step0Labels permutation96 permutation6
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw41440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41440 raw41440Labels = mixedMoment B node1805 node1805Labels := by
  calc
    mixedMoment B raw41440 raw41440Labels = mixedMoment B raw41440step0 raw41440step0Labels := by
      have ha : raw41440step0 = (fun i j => raw41440 (permutation416 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41440step0 raw41440; decide +kernel
      have hl : raw41440step0Labels = raw41440Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41440 raw41440Labels permutation416 permutation6
    _ = mixedMoment B node1805 node1805Labels := by rfl

def raw41441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41441 raw41441Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw41441 raw41441Labels = mixedMoment B raw41441step0 raw41441step0Labels := by
      have ha : raw41441step0 = (fun i j => raw41441 (permutation410 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41441step0 raw41441; decide +kernel
      have hl : raw41441step0Labels = raw41441Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41441 raw41441Labels permutation410 permutation6
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw41442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw41442Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw41442step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41442 raw41442Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw41442 raw41442Labels = mixedMoment B raw41442step0 raw41442step0Labels := by
      have hz : ∀ j, raw41442 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41442step0 = (fun i j => raw41442 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41442step0 raw41442; decide +kernel
      have hl : raw41442step0Labels = raw41442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41442 raw41442Labels permutation520 hz
    mixedMoment B raw41442step0 raw41442step0Labels = mixedMoment B raw41442step1 raw41442step1Labels := by
      have ha : raw41442step1 = (fun i j => raw41442step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41442step1 raw41442step0; decide +kernel
      have hl : raw41442step1Labels = raw41442step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41442step0 raw41442step0Labels permutation96 permutation6
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw41443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw41443Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41443 raw41443Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw41443 raw41443Labels = mixedMoment B raw41443step0 raw41443step0Labels := by
      have ha : raw41443step0 = (fun i j => raw41443 (permutation396 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41443step0 raw41443; decide +kernel
      have hl : raw41443step0Labels = raw41443Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41443 raw41443Labels permutation396 permutation6
    _ = mixedMoment B node3787 node3787Labels := by rfl

def raw41444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw41444Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41444 raw41444Labels = mixedMoment B node3671 node3671Labels := by
  calc
    mixedMoment B raw41444 raw41444Labels = mixedMoment B raw41444step0 raw41444step0Labels := by
      have ha : raw41444step0 = (fun i j => raw41444 (permutation530 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41444step0 raw41444; decide +kernel
      have hl : raw41444step0Labels = raw41444Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41444 raw41444Labels permutation530 permutation6
    mixedMoment B raw41444step0 raw41444step0Labels = mixedMoment B raw41444step1 raw41444step1Labels := by
      have ha : raw41444step1 = -raw41444step0 := by apply Matrix.ext; change ∀ i j, raw41444step1 i j = -(raw41444step0 i j); unfold raw41444step1 raw41444step0; decide +kernel
      have hl : raw41444step1Labels = raw41444step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3671 node3671Labels := by rfl

def raw41445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41445Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41445 raw41445Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw41445 raw41445Labels = mixedMoment B raw41445step0 raw41445step0Labels := by
      have ha : raw41445step0 = (fun i j => raw41445 (permutation390 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41445step0 raw41445; decide +kernel
      have hl : raw41445step0Labels = raw41445Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41445 raw41445Labels permutation390 permutation6
    _ = mixedMoment B node3781 node3781Labels := by rfl

def raw41446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41446Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41446 raw41446Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw41446 raw41446Labels = mixedMoment B raw41446step0 raw41446step0Labels := by
      have ha : raw41446step0 = (fun i j => raw41446 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41446step0 raw41446; decide +kernel
      have hl : raw41446step0Labels = raw41446Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41446 raw41446Labels permutation393 permutation6
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw41447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41447Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![2, 1, -3]]
def raw41447step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41447 raw41447Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw41447 raw41447Labels = mixedMoment B raw41447step0 raw41447step0Labels := by
      have hz : ∀ j, raw41447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41447step0 = (fun i j => raw41447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41447step0 raw41447; decide +kernel
      have hl : raw41447step0Labels = raw41447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41447 raw41447Labels permutation434 hz
    mixedMoment B raw41447step0 raw41447step0Labels = mixedMoment B raw41447step1 raw41447step1Labels := by
      have ha : raw41447step1 = (fun i j => raw41447step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41447step1 raw41447step0; decide +kernel
      have hl : raw41447step1Labels = raw41447step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41447step0 raw41447step0Labels permutation140 permutation6
    _ = mixedMoment B node2813 node2813Labels := by rfl

def raw41448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw41448Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41448step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41448 raw41448Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw41448 raw41448Labels = mixedMoment B raw41448step0 raw41448step0Labels := by
      have hz : ∀ j, raw41448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41448step0 = (fun i j => raw41448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41448step0 raw41448; decide +kernel
      have hl : raw41448step0Labels = raw41448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41448 raw41448Labels permutation434 hz
    mixedMoment B raw41448step0 raw41448step0Labels = mixedMoment B raw41448step1 raw41448step1Labels := by
      have ha : raw41448step1 = (fun i j => raw41448step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41448step1 raw41448step0; decide +kernel
      have hl : raw41448step1Labels = raw41448step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41448step0 raw41448step0Labels permutation93 permutation6
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw41449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw41449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41449 raw41449Labels = mixedMoment B node2809 node2809Labels := by
  calc
    mixedMoment B raw41449 raw41449Labels = mixedMoment B raw41449step0 raw41449step0Labels := by
      have ha : raw41449step0 = (fun i j => raw41449 (permutation626 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41449step0 raw41449; decide +kernel
      have hl : raw41449step0Labels = raw41449Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41449 raw41449Labels permutation626 permutation6
    _ = mixedMoment B node2809 node2809Labels := by rfl

def raw41450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw41450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41450 raw41450Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw41450 raw41450Labels = mixedMoment B raw41450step0 raw41450step0Labels := by
      have ha : raw41450step0 = (fun i j => raw41450 (permutation410 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41450step0 raw41450; decide +kernel
      have hl : raw41450step0Labels = raw41450Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41450 raw41450Labels permutation410 permutation6
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw41451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw41451Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41451 raw41451Labels = mixedMoment B node3670 node3670Labels := by
  calc
    mixedMoment B raw41451 raw41451Labels = mixedMoment B raw41451step0 raw41451step0Labels := by
      have ha : raw41451step0 = (fun i j => raw41451 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41451step0 raw41451; decide +kernel
      have hl : raw41451step0Labels = raw41451Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41451 raw41451Labels permutation409 permutation6
    _ = mixedMoment B node3670 node3670Labels := by rfl

def raw41452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw41452Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw41452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw41452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41452 raw41452Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw41452 raw41452Labels = mixedMoment B raw41452step0 raw41452step0Labels := by
      have ha : raw41452step0 = (fun i j => raw41452 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41452step0 raw41452; decide +kernel
      have hl : raw41452step0Labels = raw41452Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41452 raw41452Labels permutation640 permutation3
    mixedMoment B raw41452step0 raw41452step0Labels = mixedMoment B raw41452step1 raw41452step1Labels := by
      have ha : raw41452step1 = -raw41452step0 := by apply Matrix.ext; change ∀ i j, raw41452step1 i j = -(raw41452step0 i j); unfold raw41452step1 raw41452step0; decide +kernel
      have hl : raw41452step1Labels = raw41452step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3909 node3909Labels := by rfl

def raw41453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, 1, -3]]
def raw41453Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41453 raw41453Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw41453 raw41453Labels = mixedMoment B raw41453step0 raw41453step0Labels := by
      have ha : raw41453step0 = (fun i j => raw41453 (permutation635 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41453step0 raw41453; decide +kernel
      have hl : raw41453step0Labels = raw41453Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41453 raw41453Labels permutation635 permutation6
    _ = mixedMoment B node2893 node2893Labels := by rfl

def raw41454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw41454Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41454 raw41454Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw41454 raw41454Labels = mixedMoment B raw41454step0 raw41454step0Labels := by
      have ha : raw41454step0 = (fun i j => raw41454 (permutation333 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41454step0 raw41454; decide +kernel
      have hl : raw41454step0Labels = raw41454Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41454 raw41454Labels permutation333 permutation6
    mixedMoment B raw41454step0 raw41454step0Labels = mixedMoment B raw41454step1 raw41454step1Labels := by
      have ha : raw41454step1 = -raw41454step0 := by apply Matrix.ext; change ∀ i j, raw41454step1 i j = -(raw41454step0 i j); unfold raw41454step1 raw41454step0; decide +kernel
      have hl : raw41454step1Labels = raw41454step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3945 node3945Labels := by rfl

def raw41455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw41455Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![2, 2, -4]]
def raw41455step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41455 raw41455Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw41455 raw41455Labels = mixedMoment B raw41455step0 raw41455step0Labels := by
      have hz : ∀ j, raw41455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41455step0 = (fun i j => raw41455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41455step0 raw41455; decide +kernel
      have hl : raw41455step0Labels = raw41455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41455 raw41455Labels permutation434 hz
    mixedMoment B raw41455step0 raw41455step0Labels = mixedMoment B raw41455step1 raw41455step1Labels := by
      have ha : raw41455step1 = (fun i j => raw41455step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41455step1 raw41455step0; decide +kernel
      have hl : raw41455step1Labels = raw41455step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41455step0 raw41455step0Labels permutation140 permutation6
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw41456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw41456Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -2, 1]]
def raw41456step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41456 raw41456Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw41456 raw41456Labels = mixedMoment B raw41456step0 raw41456step0Labels := by
      have hz : ∀ j, raw41456 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41456step0 = (fun i j => raw41456 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41456step0 raw41456; decide +kernel
      have hl : raw41456step0Labels = raw41456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41456 raw41456Labels permutation434 hz
    mixedMoment B raw41456step0 raw41456step0Labels = mixedMoment B raw41456step1 raw41456step1Labels := by
      have ha : raw41456step1 = (fun i j => raw41456step0 (permutation117 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41456step1 raw41456step0; decide +kernel
      have hl : raw41456step1Labels = raw41456step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41456step0 raw41456step0Labels permutation117 permutation6
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw41457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 2, -4]]
def raw41457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41457 raw41457Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw41457 raw41457Labels = mixedMoment B raw41457step0 raw41457step0Labels := by
      have ha : raw41457step0 = (fun i j => raw41457 (permutation626 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41457step0 raw41457; decide +kernel
      have hl : raw41457step0Labels = raw41457Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41457 raw41457Labels permutation626 permutation6
    _ = mixedMoment B node1129 node1129Labels := by rfl

def raw41458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw41458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41458 raw41458Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw41458 raw41458Labels = mixedMoment B raw41458step0 raw41458step0Labels := by
      have ha : raw41458step0 = (fun i j => raw41458 (permutation548 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41458step0 raw41458; decide +kernel
      have hl : raw41458step0Labels = raw41458Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41458 raw41458Labels permutation548 permutation6
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw41459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw41459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41459 raw41459Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw41459 raw41459Labels = mixedMoment B raw41459step0 raw41459step0Labels := by
      have ha : raw41459step0 = (fun i j => raw41459 (permutation547 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41459step0 raw41459; decide +kernel
      have hl : raw41459step0Labels = raw41459Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41459 raw41459Labels permutation547 permutation6
    _ = mixedMoment B node2428 node2428Labels := by rfl

def raw41460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw41460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw41460step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2], ![2, 3, -5]]
def raw41460step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41460step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41460 raw41460Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw41460 raw41460Labels = mixedMoment B raw41460step0 raw41460step0Labels := by
      have hz : ∀ j, raw41460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41460step0 = (fun i j => raw41460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41460step0 raw41460; decide +kernel
      have hl : raw41460step0Labels = raw41460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41460 raw41460Labels permutation434 hz
    mixedMoment B raw41460step0 raw41460step0Labels = mixedMoment B raw41460step1 raw41460step1Labels := by
      have hz : ∀ j, raw41460step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41460step1 = (fun i j => raw41460step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41460step1 raw41460step0; decide +kernel
      have hl : raw41460step1Labels = raw41460step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41460step0 raw41460step0Labels permutation80 hz
    mixedMoment B raw41460step1 raw41460step1Labels = mixedMoment B raw41460step2 raw41460step2Labels := by
      have ha : raw41460step2 = (fun i j => raw41460step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41460step2 raw41460step1; decide +kernel
      have hl : raw41460step2Labels = raw41460step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41460step1 raw41460step1Labels permutation26 permutation6
    _ = mixedMoment B node608 node608Labels := by rfl

def raw41461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw41461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw41461step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41461 raw41461Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw41461 raw41461Labels = mixedMoment B raw41461step0 raw41461step0Labels := by
      have hz : ∀ j, raw41461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41461step0 = (fun i j => raw41461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41461step0 raw41461; decide +kernel
      have hl : raw41461step0Labels = raw41461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41461 raw41461Labels permutation346 hz
    mixedMoment B raw41461step0 raw41461step0Labels = mixedMoment B raw41461step1 raw41461step1Labels := by
      have ha : raw41461step1 = (fun i j => raw41461step0 (permutation131 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41461step1 raw41461step0; decide +kernel
      have hl : raw41461step1Labels = raw41461step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41461step0 raw41461step0Labels permutation131 permutation6
    _ = mixedMoment B node603 node603Labels := by rfl

def raw41462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw41462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw41462step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41462 raw41462Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw41462 raw41462Labels = mixedMoment B raw41462step0 raw41462step0Labels := by
      have hz : ∀ j, raw41462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41462step0 = (fun i j => raw41462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41462step0 raw41462; decide +kernel
      have hl : raw41462step0Labels = raw41462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41462 raw41462Labels permutation346 hz
    mixedMoment B raw41462step0 raw41462step0Labels = mixedMoment B raw41462step1 raw41462step1Labels := by
      have ha : raw41462step1 = (fun i j => raw41462step0 (permutation123 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41462step1 raw41462step0; decide +kernel
      have hl : raw41462step1Labels = raw41462step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41462step0 raw41462step0Labels permutation123 permutation6
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw41463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw41463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw41463step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41463 raw41463Labels = mixedMoment B node2337 node2337Labels := by
  calc
    mixedMoment B raw41463 raw41463Labels = mixedMoment B raw41463step0 raw41463step0Labels := by
      have hz : ∀ j, raw41463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41463step0 = (fun i j => raw41463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41463step0 raw41463; decide +kernel
      have hl : raw41463step0Labels = raw41463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41463 raw41463Labels permutation346 hz
    mixedMoment B raw41463step0 raw41463step0Labels = mixedMoment B raw41463step1 raw41463step1Labels := by
      have ha : raw41463step1 = (fun i j => raw41463step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41463step1 raw41463step0; decide +kernel
      have hl : raw41463step1Labels = raw41463step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41463step0 raw41463step0Labels permutation122 permutation6
    _ = mixedMoment B node2337 node2337Labels := by rfl

def raw41464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41464 raw41464Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw41464 raw41464Labels = mixedMoment B raw41464step0 raw41464step0Labels := by
      have ha : raw41464step0 = (fun i j => raw41464 (permutation572 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41464step0 raw41464; decide +kernel
      have hl : raw41464step0Labels = raw41464Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41464 raw41464Labels permutation572 permutation6
    _ = mixedMoment B node922 node922Labels := by rfl

def raw41465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41465 raw41465Labels = mixedMoment B node2332 node2332Labels := by
  calc
    mixedMoment B raw41465 raw41465Labels = mixedMoment B raw41465step0 raw41465step0Labels := by
      have ha : raw41465step0 = (fun i j => raw41465 (permutation572 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41465step0 raw41465; decide +kernel
      have hl : raw41465step0Labels = raw41465Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41465 raw41465Labels permutation572 permutation6
    _ = mixedMoment B node2332 node2332Labels := by rfl

def raw41466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![2, -1, -1]]
def raw41466step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![2, -1, -1]]
def raw41466step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw41466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41466 raw41466Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw41466 raw41466Labels = mixedMoment B raw41466step0 raw41466step0Labels := by
      have hz : ∀ j, raw41466 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41466step0 = (fun i j => raw41466 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41466step0 raw41466; decide +kernel
      have hl : raw41466step0Labels = raw41466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41466 raw41466Labels permutation520 hz
    mixedMoment B raw41466step0 raw41466step0Labels = mixedMoment B raw41466step1 raw41466step1Labels := by
      have hz : ∀ j, raw41466step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41466step1 = (fun i j => raw41466step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41466step1 raw41466step0; decide +kernel
      have hl : raw41466step1Labels = raw41466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41466step0 raw41466step0Labels permutation104 hz
    mixedMoment B raw41466step1 raw41466step1Labels = mixedMoment B raw41466step2 raw41466step2Labels := by
      have ha : raw41466step2 = (fun i j => raw41466step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41466step2 raw41466step1; decide +kernel
      have hl : raw41466step2Labels = raw41466step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41466step1 raw41466step1Labels permutation24 permutation6
    _ = mixedMoment B node2109 node2109Labels := by rfl

def raw41467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, -1, 1], ![2, 0, -2]]
def raw41467step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41467step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41467 raw41467Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw41467 raw41467Labels = mixedMoment B raw41467step0 raw41467step0Labels := by
      have hz : ∀ j, raw41467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41467step0 = (fun i j => raw41467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41467step0 raw41467; decide +kernel
      have hl : raw41467step0Labels = raw41467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41467 raw41467Labels permutation434 hz
    mixedMoment B raw41467step0 raw41467step0Labels = mixedMoment B raw41467step1 raw41467step1Labels := by
      have ha : raw41467step1 = (fun i j => raw41467step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41467step1 raw41467step0; decide +kernel
      have hl : raw41467step1Labels = raw41467step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41467step0 raw41467step0Labels permutation99 permutation6
    _ = mixedMoment B node1807 node1807Labels := by rfl

def raw41468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw41468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41468 raw41468Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw41468 raw41468Labels = mixedMoment B raw41468step0 raw41468step0Labels := by
      have hz : ∀ j, raw41468 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41468step0 = (fun i j => raw41468 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41468step0 raw41468; decide +kernel
      have hl : raw41468step0Labels = raw41468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41468 raw41468Labels permutation434 hz
    mixedMoment B raw41468step0 raw41468step0Labels = mixedMoment B raw41468step1 raw41468step1Labels := by
      have ha : raw41468step1 = (fun i j => raw41468step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41468step1 raw41468step0; decide +kernel
      have hl : raw41468step1Labels = raw41468step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41468step0 raw41468step0Labels permutation96 permutation6
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw41469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw41469Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]
def raw41469step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw41469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41469step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41469 raw41469Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw41469 raw41469Labels = mixedMoment B raw41469step0 raw41469step0Labels := by
      have hz : ∀ j, raw41469 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41469step0 = (fun i j => raw41469 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41469step0 raw41469; decide +kernel
      have hl : raw41469step0Labels = raw41469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41469 raw41469Labels permutation520 hz
    mixedMoment B raw41469step0 raw41469step0Labels = mixedMoment B raw41469step1 raw41469step1Labels := by
      have ha : raw41469step1 = (fun i j => raw41469step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41469step1 raw41469step0; decide +kernel
      have hl : raw41469step1Labels = raw41469step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41469step0 raw41469step0Labels permutation61 permutation6
    mixedMoment B raw41469step1 raw41469step1Labels = mixedMoment B raw41469step2 raw41469step2Labels := by
      have ha : raw41469step2 = -raw41469step1 := by apply Matrix.ext; change ∀ i j, raw41469step2 i j = -(raw41469step1 i j); unfold raw41469step2 raw41469step1; decide +kernel
      have hl : raw41469step2Labels = raw41469step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw41470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw41470Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41470 raw41470Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw41470 raw41470Labels = mixedMoment B raw41470step0 raw41470step0Labels := by
      have ha : raw41470step0 = (fun i j => raw41470 (permutation323 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41470step0 raw41470; decide +kernel
      have hl : raw41470step0Labels = raw41470Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41470 raw41470Labels permutation323 permutation6
    mixedMoment B raw41470step0 raw41470step0Labels = mixedMoment B raw41470step1 raw41470step1Labels := by
      have ha : raw41470step1 = -raw41470step0 := by apply Matrix.ext; change ∀ i j, raw41470step1 i j = -(raw41470step0 i j); unfold raw41470step1 raw41470step0; decide +kernel
      have hl : raw41470step1Labels = raw41470step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2431 node2431Labels := by rfl

def raw41471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41471Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41471 raw41471Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw41471 raw41471Labels = mixedMoment B raw41471step0 raw41471step0Labels := by
      have ha : raw41471step0 = (fun i j => raw41471 (permutation288 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41471step0 raw41471; decide +kernel
      have hl : raw41471step0Labels = raw41471Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41471 raw41471Labels permutation288 permutation6
    mixedMoment B raw41471step0 raw41471step0Labels = mixedMoment B raw41471step1 raw41471step1Labels := by
      have ha : raw41471step1 = -raw41471step0 := by apply Matrix.ext; change ∀ i j, raw41471step1 i j = -(raw41471step0 i j); unfold raw41471step1 raw41471step0; decide +kernel
      have hl : raw41471step1Labels = raw41471step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2553 node2553Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
