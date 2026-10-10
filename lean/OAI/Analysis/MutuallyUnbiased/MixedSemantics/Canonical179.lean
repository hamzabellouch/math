import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22912 raw22912Labels = mixedMoment B node1900 node1900Labels := by
  calc
    mixedMoment B raw22912 raw22912Labels = mixedMoment B raw22912step0 raw22912step0Labels := by
      have ha : raw22912step0 = (fun i j => raw22912 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22912step0 raw22912; decide +kernel
      have hl : raw22912step0Labels = raw22912Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22912 raw22912Labels permutation201 permutation2
    _ = mixedMoment B node1900 node1900Labels := by rfl

def raw22913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw22913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22913 raw22913Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw22913 raw22913Labels = mixedMoment B raw22913step0 raw22913step0Labels := by
      have ha : raw22913step0 = (fun i j => raw22913 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22913step0 raw22913; decide +kernel
      have hl : raw22913step0Labels = raw22913Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22913 raw22913Labels permutation200 permutation2
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw22914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw22914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22914 raw22914Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw22914 raw22914Labels = mixedMoment B raw22914step0 raw22914step0Labels := by
      have ha : raw22914step0 = (fun i j => raw22914 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22914step0 raw22914; decide +kernel
      have hl : raw22914step0Labels = raw22914Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22914 raw22914Labels permutation201 permutation2
    _ = mixedMoment B node2190 node2190Labels := by rfl

def raw22915 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![2, -2], ![0, 0]]
def raw22915Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22915step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![2, -2]]
def raw22915step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22915step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw22915step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22915 raw22915Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw22915 raw22915Labels = mixedMoment B raw22915step0 raw22915step0Labels := by
      have hz : ∀ j, raw22915 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw22915step0 = (fun i j => raw22915 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw22915step0 raw22915; decide +kernel
      have hl : raw22915step0Labels = raw22915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22915 raw22915Labels permutation590 hz
    mixedMoment B raw22915step0 raw22915step0Labels = mixedMoment B raw22915step1 raw22915step1Labels := by
      have ha : raw22915step1 = (fun i j => raw22915step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22915step1 raw22915step0; decide +kernel
      have hl : raw22915step1Labels = raw22915step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22915step0 raw22915step0Labels permutation44 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw22916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22916 raw22916Labels = mixedMoment B node2073 node2073Labels := by
  calc
    mixedMoment B raw22916 raw22916Labels = mixedMoment B raw22916step0 raw22916step0Labels := by
      have ha : raw22916step0 = (fun i j => raw22916 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22916step0 raw22916; decide +kernel
      have hl : raw22916step0Labels = raw22916Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22916 raw22916Labels permutation158 permutation2
    _ = mixedMoment B node2073 node2073Labels := by rfl

def raw22917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22917 raw22917Labels = mixedMoment B node2073 node2073Labels := by
  calc
    mixedMoment B raw22917 raw22917Labels = mixedMoment B raw22917step0 raw22917step0Labels := by
      have ha : raw22917step0 = (fun i j => raw22917 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22917step0 raw22917; decide +kernel
      have hl : raw22917step0Labels = raw22917Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22917 raw22917Labels permutation182 permutation2
    _ = mixedMoment B node2073 node2073Labels := by rfl

def raw22918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22918 raw22918Labels = mixedMoment B node1901 node1901Labels := by
  calc
    mixedMoment B raw22918 raw22918Labels = mixedMoment B raw22918step0 raw22918step0Labels := by
      have ha : raw22918step0 = (fun i j => raw22918 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22918step0 raw22918; decide +kernel
      have hl : raw22918step0Labels = raw22918Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22918 raw22918Labels permutation200 permutation2
    _ = mixedMoment B node1901 node1901Labels := by rfl

def raw22919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw22919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22919 raw22919Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw22919 raw22919Labels = mixedMoment B raw22919step0 raw22919step0Labels := by
      have ha : raw22919step0 = (fun i j => raw22919 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22919step0 raw22919; decide +kernel
      have hl : raw22919step0Labels = raw22919Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22919 raw22919Labels permutation201 permutation2
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw22920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 1, -3], ![2, -3, 1]]
def raw22920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw22920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22920 raw22920Labels = mixedMoment B node1048 node1048Labels := by
  calc
    mixedMoment B raw22920 raw22920Labels = mixedMoment B raw22920step0 raw22920step0Labels := by
      have hz : ∀ j, raw22920 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22920step0 = (fun i j => raw22920 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22920step0 raw22920; decide +kernel
      have hl : raw22920step0Labels = raw22920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22920 raw22920Labels permutation434 hz
    mixedMoment B raw22920step0 raw22920step0Labels = mixedMoment B raw22920step1 raw22920step1Labels := by
      have hz : ∀ j, raw22920step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22920step1 = (fun i j => raw22920step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22920step1 raw22920step0; decide +kernel
      have hl : raw22920step1Labels = raw22920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22920step0 raw22920step0Labels permutation80 hz
    mixedMoment B raw22920step1 raw22920step1Labels = mixedMoment B raw22920step2 raw22920step2Labels := by
      have ha : raw22920step2 = (fun i j => raw22920step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22920step2 raw22920step1; decide +kernel
      have hl : raw22920step2Labels = raw22920step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22920step1 raw22920step1Labels permutation9 permutation2
    _ = mixedMoment B node1048 node1048Labels := by rfl

def raw22921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 1, -3], ![2, -3, 1]]
def raw22921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def raw22921step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22921 raw22921Labels = mixedMoment B node2114 node2114Labels := by
  calc
    mixedMoment B raw22921 raw22921Labels = mixedMoment B raw22921step0 raw22921step0Labels := by
      have hz : ∀ j, raw22921 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22921step0 = (fun i j => raw22921 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22921step0 raw22921; decide +kernel
      have hl : raw22921step0Labels = raw22921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22921 raw22921Labels permutation434 hz
    mixedMoment B raw22921step0 raw22921step0Labels = mixedMoment B raw22921step1 raw22921step1Labels := by
      have hz : ∀ j, raw22921step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22921step1 = (fun i j => raw22921step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22921step1 raw22921step0; decide +kernel
      have hl : raw22921step1Labels = raw22921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22921step0 raw22921step0Labels permutation80 hz
    mixedMoment B raw22921step1 raw22921step1Labels = mixedMoment B raw22921step2 raw22921step2Labels := by
      have ha : raw22921step2 = (fun i j => raw22921step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22921step2 raw22921step1; decide +kernel
      have hl : raw22921step2Labels = raw22921step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22921step1 raw22921step1Labels permutation9 permutation2
    _ = mixedMoment B node2114 node2114Labels := by rfl

def raw22922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw22922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22922 raw22922Labels = mixedMoment B node2027 node2027Labels := by
  calc
    mixedMoment B raw22922 raw22922Labels = mixedMoment B raw22922step0 raw22922step0Labels := by
      have hz : ∀ j, raw22922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22922step0 = (fun i j => raw22922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22922step0 raw22922; decide +kernel
      have hl : raw22922step0Labels = raw22922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22922 raw22922Labels permutation434 hz
    mixedMoment B raw22922step0 raw22922step0Labels = mixedMoment B raw22922step1 raw22922step1Labels := by
      have ha : raw22922step1 = (fun i j => raw22922step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22922step1 raw22922step0; decide +kernel
      have hl : raw22922step1Labels = raw22922step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22922step0 raw22922step0Labels permutation39 permutation2
    _ = mixedMoment B node2027 node2027Labels := by rfl

def raw22923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 1, -3], ![2, -3, 1]]
def raw22923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw22923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22923 raw22923Labels = mixedMoment B node2027 node2027Labels := by
  calc
    mixedMoment B raw22923 raw22923Labels = mixedMoment B raw22923step0 raw22923step0Labels := by
      have hz : ∀ j, raw22923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22923step0 = (fun i j => raw22923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22923step0 raw22923; decide +kernel
      have hl : raw22923step0Labels = raw22923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22923 raw22923Labels permutation346 hz
    mixedMoment B raw22923step0 raw22923step0Labels = mixedMoment B raw22923step1 raw22923step1Labels := by
      have ha : raw22923step1 = (fun i j => raw22923step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22923step1 raw22923step0; decide +kernel
      have hl : raw22923step1Labels = raw22923step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22923step0 raw22923step0Labels permutation39 permutation2
    _ = mixedMoment B node2027 node2027Labels := by rfl

def raw22924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw22924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw22924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw22924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22924 raw22924Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw22924 raw22924Labels = mixedMoment B raw22924step0 raw22924step0Labels := by
      have hz : ∀ j, raw22924 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22924step0 = (fun i j => raw22924 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22924step0 raw22924; decide +kernel
      have hl : raw22924step0Labels = raw22924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22924 raw22924Labels permutation434 hz
    mixedMoment B raw22924step0 raw22924step0Labels = mixedMoment B raw22924step1 raw22924step1Labels := by
      have hz : ∀ j, raw22924step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22924step1 = (fun i j => raw22924step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22924step1 raw22924step0; decide +kernel
      have hl : raw22924step1Labels = raw22924step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22924step0 raw22924step0Labels permutation80 hz
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw22925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw22925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3], ![1, -2, 1]]
def raw22925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 1, -3], ![1, -2, 1]]
def raw22925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw22925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22925 raw22925Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw22925 raw22925Labels = mixedMoment B raw22925step0 raw22925step0Labels := by
      have hz : ∀ j, raw22925 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22925step0 = (fun i j => raw22925 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22925step0 raw22925; decide +kernel
      have hl : raw22925step0Labels = raw22925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22925 raw22925Labels permutation434 hz
    mixedMoment B raw22925step0 raw22925step0Labels = mixedMoment B raw22925step1 raw22925step1Labels := by
      have hz : ∀ j, raw22925step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22925step1 = (fun i j => raw22925step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22925step1 raw22925step0; decide +kernel
      have hl : raw22925step1Labels = raw22925step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22925step0 raw22925step0Labels permutation80 hz
    mixedMoment B raw22925step1 raw22925step1Labels = mixedMoment B raw22925step2 raw22925step2Labels := by
      have ha : raw22925step2 = (fun i j => raw22925step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22925step2 raw22925step1; decide +kernel
      have hl : raw22925step2Labels = raw22925step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22925step1 raw22925step1Labels permutation9 permutation2
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw22926 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![3, -3], ![-1, 1]]
def raw22926Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22926step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![3, -3], ![-1, 1]]
def raw22926step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22926step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![3, -3], ![-1, 1]]
def raw22926step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22926step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw22926step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22926 raw22926Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw22926 raw22926Labels = mixedMoment B raw22926step0 raw22926step0Labels := by
      have hz : ∀ j, raw22926 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22926step0 = (fun i j => raw22926 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22926step0 raw22926; decide +kernel
      have hl : raw22926step0Labels = raw22926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22926 raw22926Labels permutation434 hz
    mixedMoment B raw22926step0 raw22926step0Labels = mixedMoment B raw22926step1 raw22926step1Labels := by
      have hz : ∀ j, raw22926step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22926step1 = (fun i j => raw22926step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22926step1 raw22926step0; decide +kernel
      have hl : raw22926step1Labels = raw22926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22926step0 raw22926step0Labels permutation80 hz
    mixedMoment B raw22926step1 raw22926step1Labels = mixedMoment B raw22926step2 raw22926step2Labels := by
      have ha : raw22926step2 = (fun i j => raw22926step1 (permutation12 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22926step2 raw22926step1; decide +kernel
      have hl : raw22926step2Labels = raw22926step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22926step1 raw22926step1Labels permutation12 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw22927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22927step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22927step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22927 raw22927Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw22927 raw22927Labels = mixedMoment B raw22927step0 raw22927step0Labels := by
      have hz : ∀ j, raw22927 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22927step0 = (fun i j => raw22927 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22927step0 raw22927; decide +kernel
      have hl : raw22927step0Labels = raw22927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22927 raw22927Labels permutation434 hz
    mixedMoment B raw22927step0 raw22927step0Labels = mixedMoment B raw22927step1 raw22927step1Labels := by
      have hz : ∀ j, raw22927step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22927step1 = (fun i j => raw22927step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22927step1 raw22927step0; decide +kernel
      have hl : raw22927step1Labels = raw22927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22927step0 raw22927step0Labels permutation80 hz
    mixedMoment B raw22927step1 raw22927step1Labels = mixedMoment B raw22927step2 raw22927step2Labels := by
      have ha : raw22927step2 = (fun i j => raw22927step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22927step2 raw22927step1; decide +kernel
      have hl : raw22927step2Labels = raw22927step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22927step1 raw22927step1Labels permutation9 permutation2
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw22928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22928 raw22928Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw22928 raw22928Labels = mixedMoment B raw22928step0 raw22928step0Labels := by
      have hz : ∀ j, raw22928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22928step0 = (fun i j => raw22928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22928step0 raw22928; decide +kernel
      have hl : raw22928step0Labels = raw22928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22928 raw22928Labels permutation434 hz
    mixedMoment B raw22928step0 raw22928step0Labels = mixedMoment B raw22928step1 raw22928step1Labels := by
      have ha : raw22928step1 = (fun i j => raw22928step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22928step1 raw22928step0; decide +kernel
      have hl : raw22928step1Labels = raw22928step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22928step0 raw22928step0Labels permutation39 permutation2
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw22929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22929 raw22929Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw22929 raw22929Labels = mixedMoment B raw22929step0 raw22929step0Labels := by
      have hz : ∀ j, raw22929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22929step0 = (fun i j => raw22929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22929step0 raw22929; decide +kernel
      have hl : raw22929step0Labels = raw22929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22929 raw22929Labels permutation346 hz
    mixedMoment B raw22929step0 raw22929step0Labels = mixedMoment B raw22929step1 raw22929step1Labels := by
      have ha : raw22929step1 = (fun i j => raw22929step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22929step1 raw22929step0; decide +kernel
      have hl : raw22929step1Labels = raw22929step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22929step0 raw22929step0Labels permutation39 permutation2
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw22930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22930 raw22930Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw22930 raw22930Labels = mixedMoment B raw22930step0 raw22930step0Labels := by
      have hz : ∀ j, raw22930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22930step0 = (fun i j => raw22930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22930step0 raw22930; decide +kernel
      have hl : raw22930step0Labels = raw22930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22930 raw22930Labels permutation434 hz
    mixedMoment B raw22930step0 raw22930step0Labels = mixedMoment B raw22930step1 raw22930step1Labels := by
      have hz : ∀ j, raw22930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22930step1 = (fun i j => raw22930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22930step1 raw22930step0; decide +kernel
      have hl : raw22930step1Labels = raw22930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22930step0 raw22930step0Labels permutation80 hz
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw22931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22931 raw22931Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw22931 raw22931Labels = mixedMoment B raw22931step0 raw22931step0Labels := by
      have hz : ∀ j, raw22931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22931step0 = (fun i j => raw22931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22931step0 raw22931; decide +kernel
      have hl : raw22931step0Labels = raw22931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22931 raw22931Labels permutation434 hz
    mixedMoment B raw22931step0 raw22931step0Labels = mixedMoment B raw22931step1 raw22931step1Labels := by
      have hz : ∀ j, raw22931step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22931step1 = (fun i j => raw22931step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22931step1 raw22931step0; decide +kernel
      have hl : raw22931step1Labels = raw22931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22931step0 raw22931step0Labels permutation80 hz
    mixedMoment B raw22931step1 raw22931step1Labels = mixedMoment B raw22931step2 raw22931step2Labels := by
      have ha : raw22931step2 = (fun i j => raw22931step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22931step2 raw22931step1; decide +kernel
      have hl : raw22931step2Labels = raw22931step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22931step1 raw22931step1Labels permutation9 permutation2
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw22932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22932step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22932 raw22932Labels = mixedMoment B node4185 node4185Labels := by
  calc
    mixedMoment B raw22932 raw22932Labels = mixedMoment B raw22932step0 raw22932step0Labels := by
      have hz : ∀ j, raw22932 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22932step0 = (fun i j => raw22932 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22932step0 raw22932; decide +kernel
      have hl : raw22932step0Labels = raw22932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22932 raw22932Labels permutation434 hz
    mixedMoment B raw22932step0 raw22932step0Labels = mixedMoment B raw22932step1 raw22932step1Labels := by
      have hz : ∀ j, raw22932step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22932step1 = (fun i j => raw22932step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22932step1 raw22932step0; decide +kernel
      have hl : raw22932step1Labels = raw22932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22932step0 raw22932step0Labels permutation80 hz
    mixedMoment B raw22932step1 raw22932step1Labels = mixedMoment B raw22932step2 raw22932step2Labels := by
      have ha : raw22932step2 = (fun i j => raw22932step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22932step2 raw22932step1; decide +kernel
      have hl : raw22932step2Labels = raw22932step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22932step1 raw22932step1Labels permutation9 permutation2
    _ = mixedMoment B node4185 node4185Labels := by rfl

def raw22933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22933 raw22933Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw22933 raw22933Labels = mixedMoment B raw22933step0 raw22933step0Labels := by
      have hz : ∀ j, raw22933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22933step0 = (fun i j => raw22933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22933step0 raw22933; decide +kernel
      have hl : raw22933step0Labels = raw22933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22933 raw22933Labels permutation434 hz
    mixedMoment B raw22933step0 raw22933step0Labels = mixedMoment B raw22933step1 raw22933step1Labels := by
      have ha : raw22933step1 = (fun i j => raw22933step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22933step1 raw22933step0; decide +kernel
      have hl : raw22933step1Labels = raw22933step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22933step0 raw22933step0Labels permutation39 permutation2
    _ = mixedMoment B node4354 node4354Labels := by rfl

def raw22934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22934 raw22934Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw22934 raw22934Labels = mixedMoment B raw22934step0 raw22934step0Labels := by
      have hz : ∀ j, raw22934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22934step0 = (fun i j => raw22934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22934step0 raw22934; decide +kernel
      have hl : raw22934step0Labels = raw22934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22934 raw22934Labels permutation346 hz
    mixedMoment B raw22934step0 raw22934step0Labels = mixedMoment B raw22934step1 raw22934step1Labels := by
      have ha : raw22934step1 = (fun i j => raw22934step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22934step1 raw22934step0; decide +kernel
      have hl : raw22934step1Labels = raw22934step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22934step0 raw22934step0Labels permutation39 permutation2
    _ = mixedMoment B node4354 node4354Labels := by rfl

def raw22935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22935step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22935 raw22935Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw22935 raw22935Labels = mixedMoment B raw22935step0 raw22935step0Labels := by
      have hz : ∀ j, raw22935 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22935step0 = (fun i j => raw22935 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22935step0 raw22935; decide +kernel
      have hl : raw22935step0Labels = raw22935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22935 raw22935Labels permutation434 hz
    mixedMoment B raw22935step0 raw22935step0Labels = mixedMoment B raw22935step1 raw22935step1Labels := by
      have hz : ∀ j, raw22935step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22935step1 = (fun i j => raw22935step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22935step1 raw22935step0; decide +kernel
      have hl : raw22935step1Labels = raw22935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22935step0 raw22935step0Labels permutation80 hz
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw22936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22936 raw22936Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw22936 raw22936Labels = mixedMoment B raw22936step0 raw22936step0Labels := by
      have hz : ∀ j, raw22936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22936step0 = (fun i j => raw22936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22936step0 raw22936; decide +kernel
      have hl : raw22936step0Labels = raw22936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22936 raw22936Labels permutation434 hz
    mixedMoment B raw22936step0 raw22936step0Labels = mixedMoment B raw22936step1 raw22936step1Labels := by
      have hz : ∀ j, raw22936step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22936step1 = (fun i j => raw22936step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22936step1 raw22936step0; decide +kernel
      have hl : raw22936step1Labels = raw22936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22936step0 raw22936step0Labels permutation80 hz
    mixedMoment B raw22936step1 raw22936step1Labels = mixedMoment B raw22936step2 raw22936step2Labels := by
      have ha : raw22936step2 = (fun i j => raw22936step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22936step2 raw22936step1; decide +kernel
      have hl : raw22936step2Labels = raw22936step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22936step1 raw22936step1Labels permutation12 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw22937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22937 raw22937Labels = mixedMoment B node4154 node4154Labels := by
  calc
    mixedMoment B raw22937 raw22937Labels = mixedMoment B raw22937step0 raw22937step0Labels := by
      have hz : ∀ j, raw22937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22937step0 = (fun i j => raw22937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22937step0 raw22937; decide +kernel
      have hl : raw22937step0Labels = raw22937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22937 raw22937Labels permutation434 hz
    mixedMoment B raw22937step0 raw22937step0Labels = mixedMoment B raw22937step1 raw22937step1Labels := by
      have ha : raw22937step1 = (fun i j => raw22937step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22937step1 raw22937step0; decide +kernel
      have hl : raw22937step1Labels = raw22937step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22937step0 raw22937step0Labels permutation33 permutation2
    _ = mixedMoment B node4154 node4154Labels := by rfl

def raw22938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22938 raw22938Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw22938 raw22938Labels = mixedMoment B raw22938step0 raw22938step0Labels := by
      have hz : ∀ j, raw22938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22938step0 = (fun i j => raw22938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22938step0 raw22938; decide +kernel
      have hl : raw22938step0Labels = raw22938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22938 raw22938Labels permutation434 hz
    mixedMoment B raw22938step0 raw22938step0Labels = mixedMoment B raw22938step1 raw22938step1Labels := by
      have ha : raw22938step1 = (fun i j => raw22938step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22938step1 raw22938step0; decide +kernel
      have hl : raw22938step1Labels = raw22938step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22938step0 raw22938step0Labels permutation33 permutation2
    _ = mixedMoment B node4368 node4368Labels := by rfl

def raw22939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22939 raw22939Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw22939 raw22939Labels = mixedMoment B raw22939step0 raw22939step0Labels := by
      have ha : raw22939step0 = (fun i j => raw22939 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22939step0 raw22939; decide +kernel
      have hl : raw22939step0Labels = raw22939Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22939 raw22939Labels permutation201 permutation2
    _ = mixedMoment B node4328 node4328Labels := by rfl

def raw22940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22940 raw22940Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw22940 raw22940Labels = mixedMoment B raw22940step0 raw22940step0Labels := by
      have hz : ∀ j, raw22940 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22940step0 = (fun i j => raw22940 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22940step0 raw22940; decide +kernel
      have hl : raw22940step0Labels = raw22940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22940 raw22940Labels permutation434 hz
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw22941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22941 raw22941Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw22941 raw22941Labels = mixedMoment B raw22941step0 raw22941step0Labels := by
      have hz : ∀ j, raw22941 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22941step0 = (fun i j => raw22941 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22941step0 raw22941; decide +kernel
      have hl : raw22941step0Labels = raw22941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22941 raw22941Labels permutation434 hz
    mixedMoment B raw22941step0 raw22941step0Labels = mixedMoment B raw22941step1 raw22941step1Labels := by
      have ha : raw22941step1 = (fun i j => raw22941step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22941step1 raw22941step0; decide +kernel
      have hl : raw22941step1Labels = raw22941step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22941step0 raw22941step0Labels permutation33 permutation2
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw22942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22942 raw22942Labels = mixedMoment B node4154 node4154Labels := by
  calc
    mixedMoment B raw22942 raw22942Labels = mixedMoment B raw22942step0 raw22942step0Labels := by
      have hz : ∀ j, raw22942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22942step0 = (fun i j => raw22942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22942step0 raw22942; decide +kernel
      have hl : raw22942step0Labels = raw22942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22942 raw22942Labels permutation346 hz
    mixedMoment B raw22942step0 raw22942step0Labels = mixedMoment B raw22942step1 raw22942step1Labels := by
      have ha : raw22942step1 = (fun i j => raw22942step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22942step1 raw22942step0; decide +kernel
      have hl : raw22942step1Labels = raw22942step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22942step0 raw22942step0Labels permutation33 permutation2
    _ = mixedMoment B node4154 node4154Labels := by rfl

def raw22943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22943 raw22943Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw22943 raw22943Labels = mixedMoment B raw22943step0 raw22943step0Labels := by
      have hz : ∀ j, raw22943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22943step0 = (fun i j => raw22943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22943step0 raw22943; decide +kernel
      have hl : raw22943step0Labels = raw22943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22943 raw22943Labels permutation346 hz
    mixedMoment B raw22943step0 raw22943step0Labels = mixedMoment B raw22943step1 raw22943step1Labels := by
      have ha : raw22943step1 = (fun i j => raw22943step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22943step1 raw22943step0; decide +kernel
      have hl : raw22943step1Labels = raw22943step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22943step0 raw22943step0Labels permutation33 permutation2
    _ = mixedMoment B node4368 node4368Labels := by rfl

def raw22944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22944 raw22944Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw22944 raw22944Labels = mixedMoment B raw22944step0 raw22944step0Labels := by
      have ha : raw22944step0 = (fun i j => raw22944 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22944step0 raw22944; decide +kernel
      have hl : raw22944step0Labels = raw22944Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22944 raw22944Labels permutation177 permutation2
    _ = mixedMoment B node4328 node4328Labels := by rfl

def raw22945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22945 raw22945Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw22945 raw22945Labels = mixedMoment B raw22945step0 raw22945step0Labels := by
      have hz : ∀ j, raw22945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22945step0 = (fun i j => raw22945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22945step0 raw22945; decide +kernel
      have hl : raw22945step0Labels = raw22945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22945 raw22945Labels permutation346 hz
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw22946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22946 raw22946Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw22946 raw22946Labels = mixedMoment B raw22946step0 raw22946step0Labels := by
      have hz : ∀ j, raw22946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22946step0 = (fun i j => raw22946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22946step0 raw22946; decide +kernel
      have hl : raw22946step0Labels = raw22946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22946 raw22946Labels permutation346 hz
    mixedMoment B raw22946step0 raw22946step0Labels = mixedMoment B raw22946step1 raw22946step1Labels := by
      have ha : raw22946step1 = (fun i j => raw22946step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22946step1 raw22946step0; decide +kernel
      have hl : raw22946step1Labels = raw22946step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22946step0 raw22946step0Labels permutation33 permutation2
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw22947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw22947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22947step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22947 raw22947Labels = mixedMoment B node4160 node4160Labels := by
  calc
    mixedMoment B raw22947 raw22947Labels = mixedMoment B raw22947step0 raw22947step0Labels := by
      have hz : ∀ j, raw22947 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22947step0 = (fun i j => raw22947 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22947step0 raw22947; decide +kernel
      have hl : raw22947step0Labels = raw22947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22947 raw22947Labels permutation434 hz
    mixedMoment B raw22947step0 raw22947step0Labels = mixedMoment B raw22947step1 raw22947step1Labels := by
      have hz : ∀ j, raw22947step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22947step1 = (fun i j => raw22947step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22947step1 raw22947step0; decide +kernel
      have hl : raw22947step1Labels = raw22947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22947step0 raw22947step0Labels permutation80 hz
    mixedMoment B raw22947step1 raw22947step1Labels = mixedMoment B raw22947step2 raw22947step2Labels := by
      have ha : raw22947step2 = (fun i j => raw22947step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22947step2 raw22947step1; decide +kernel
      have hl : raw22947step2Labels = raw22947step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22947step1 raw22947step1Labels permutation9 permutation2
    _ = mixedMoment B node4160 node4160Labels := by rfl

def raw22948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw22948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22948step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22948 raw22948Labels = mixedMoment B node4373 node4373Labels := by
  calc
    mixedMoment B raw22948 raw22948Labels = mixedMoment B raw22948step0 raw22948step0Labels := by
      have hz : ∀ j, raw22948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22948step0 = (fun i j => raw22948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22948step0 raw22948; decide +kernel
      have hl : raw22948step0Labels = raw22948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22948 raw22948Labels permutation434 hz
    mixedMoment B raw22948step0 raw22948step0Labels = mixedMoment B raw22948step1 raw22948step1Labels := by
      have hz : ∀ j, raw22948step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22948step1 = (fun i j => raw22948step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22948step1 raw22948step0; decide +kernel
      have hl : raw22948step1Labels = raw22948step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22948step0 raw22948step0Labels permutation80 hz
    mixedMoment B raw22948step1 raw22948step1Labels = mixedMoment B raw22948step2 raw22948step2Labels := by
      have ha : raw22948step2 = (fun i j => raw22948step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22948step2 raw22948step1; decide +kernel
      have hl : raw22948step2Labels = raw22948step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22948step1 raw22948step1Labels permutation9 permutation2
    _ = mixedMoment B node4373 node4373Labels := by rfl

def raw22949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22949step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22949 raw22949Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw22949 raw22949Labels = mixedMoment B raw22949step0 raw22949step0Labels := by
      have hz : ∀ j, raw22949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22949step0 = (fun i j => raw22949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22949step0 raw22949; decide +kernel
      have hl : raw22949step0Labels = raw22949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22949 raw22949Labels permutation434 hz
    mixedMoment B raw22949step0 raw22949step0Labels = mixedMoment B raw22949step1 raw22949step1Labels := by
      have ha : raw22949step1 = (fun i j => raw22949step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22949step1 raw22949step0; decide +kernel
      have hl : raw22949step1Labels = raw22949step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22949step0 raw22949step0Labels permutation39 permutation2
    _ = mixedMoment B node4334 node4334Labels := by rfl

def raw22950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw22950step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22950 raw22950Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw22950 raw22950Labels = mixedMoment B raw22950step0 raw22950step0Labels := by
      have hz : ∀ j, raw22950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22950step0 = (fun i j => raw22950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22950step0 raw22950; decide +kernel
      have hl : raw22950step0Labels = raw22950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22950 raw22950Labels permutation346 hz
    mixedMoment B raw22950step0 raw22950step0Labels = mixedMoment B raw22950step1 raw22950step1Labels := by
      have ha : raw22950step1 = (fun i j => raw22950step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22950step1 raw22950step0; decide +kernel
      have hl : raw22950step1Labels = raw22950step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22950step0 raw22950step0Labels permutation39 permutation2
    _ = mixedMoment B node4334 node4334Labels := by rfl

def raw22951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw22951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw22951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw22951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22951 raw22951Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw22951 raw22951Labels = mixedMoment B raw22951step0 raw22951step0Labels := by
      have hz : ∀ j, raw22951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22951step0 = (fun i j => raw22951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22951step0 raw22951; decide +kernel
      have hl : raw22951step0Labels = raw22951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22951 raw22951Labels permutation434 hz
    mixedMoment B raw22951step0 raw22951step0Labels = mixedMoment B raw22951step1 raw22951step1Labels := by
      have hz : ∀ j, raw22951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22951step1 = (fun i j => raw22951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22951step1 raw22951step0; decide +kernel
      have hl : raw22951step1Labels = raw22951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22951step0 raw22951step0Labels permutation80 hz
    mixedMoment B raw22951step1 raw22951step1Labels = mixedMoment B raw22951step2 raw22951step2Labels := by
      have ha : raw22951step2 = (fun i j => raw22951step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22951step2 raw22951step1; decide +kernel
      have hl : raw22951step2Labels = raw22951step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22951step1 raw22951step1Labels permutation9 permutation2
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw22952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22952 raw22952Labels = mixedMoment B node4162 node4162Labels := by
  calc
    mixedMoment B raw22952 raw22952Labels = mixedMoment B raw22952step0 raw22952step0Labels := by
      have hz : ∀ j, raw22952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22952step0 = (fun i j => raw22952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22952step0 raw22952; decide +kernel
      have hl : raw22952step0Labels = raw22952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22952 raw22952Labels permutation434 hz
    mixedMoment B raw22952step0 raw22952step0Labels = mixedMoment B raw22952step1 raw22952step1Labels := by
      have hz : ∀ j, raw22952step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22952step1 = (fun i j => raw22952step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22952step1 raw22952step0; decide +kernel
      have hl : raw22952step1Labels = raw22952step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22952step0 raw22952step0Labels permutation80 hz
    _ = mixedMoment B node4162 node4162Labels := by rfl

def raw22953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22953 raw22953Labels = mixedMoment B node4375 node4375Labels := by
  calc
    mixedMoment B raw22953 raw22953Labels = mixedMoment B raw22953step0 raw22953step0Labels := by
      have hz : ∀ j, raw22953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22953step0 = (fun i j => raw22953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22953step0 raw22953; decide +kernel
      have hl : raw22953step0Labels = raw22953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22953 raw22953Labels permutation434 hz
    mixedMoment B raw22953step0 raw22953step0Labels = mixedMoment B raw22953step1 raw22953step1Labels := by
      have hz : ∀ j, raw22953step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22953step1 = (fun i j => raw22953step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22953step1 raw22953step0; decide +kernel
      have hl : raw22953step1Labels = raw22953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22953step0 raw22953step0Labels permutation80 hz
    _ = mixedMoment B node4375 node4375Labels := by rfl

def raw22954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22954step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22954 raw22954Labels = mixedMoment B node4336 node4336Labels := by
  calc
    mixedMoment B raw22954 raw22954Labels = mixedMoment B raw22954step0 raw22954step0Labels := by
      have hz : ∀ j, raw22954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22954step0 = (fun i j => raw22954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22954step0 raw22954; decide +kernel
      have hl : raw22954step0Labels = raw22954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22954 raw22954Labels permutation434 hz
    mixedMoment B raw22954step0 raw22954step0Labels = mixedMoment B raw22954step1 raw22954step1Labels := by
      have ha : raw22954step1 = (fun i j => raw22954step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22954step1 raw22954step0; decide +kernel
      have hl : raw22954step1Labels = raw22954step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22954step0 raw22954step0Labels permutation38 permutation2
    _ = mixedMoment B node4336 node4336Labels := by rfl

def raw22955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22955step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22955 raw22955Labels = mixedMoment B node4336 node4336Labels := by
  calc
    mixedMoment B raw22955 raw22955Labels = mixedMoment B raw22955step0 raw22955step0Labels := by
      have hz : ∀ j, raw22955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22955step0 = (fun i j => raw22955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22955step0 raw22955; decide +kernel
      have hl : raw22955step0Labels = raw22955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22955 raw22955Labels permutation346 hz
    mixedMoment B raw22955step0 raw22955step0Labels = mixedMoment B raw22955step1 raw22955step1Labels := by
      have ha : raw22955step1 = (fun i j => raw22955step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22955step1 raw22955step0; decide +kernel
      have hl : raw22955step1Labels = raw22955step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22955step0 raw22955step0Labels permutation38 permutation2
    _ = mixedMoment B node4336 node4336Labels := by rfl

def raw22956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw22956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22956 raw22956Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw22956 raw22956Labels = mixedMoment B raw22956step0 raw22956step0Labels := by
      have hz : ∀ j, raw22956 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22956step0 = (fun i j => raw22956 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22956step0 raw22956; decide +kernel
      have hl : raw22956step0Labels = raw22956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22956 raw22956Labels permutation434 hz
    mixedMoment B raw22956step0 raw22956step0Labels = mixedMoment B raw22956step1 raw22956step1Labels := by
      have hz : ∀ j, raw22956step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22956step1 = (fun i j => raw22956step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22956step1 raw22956step0; decide +kernel
      have hl : raw22956step1Labels = raw22956step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22956step0 raw22956step0Labels permutation80 hz
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw22957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22957step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22957 raw22957Labels = mixedMoment B node3187 node3187Labels := by
  calc
    mixedMoment B raw22957 raw22957Labels = mixedMoment B raw22957step0 raw22957step0Labels := by
      have hz : ∀ j, raw22957 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22957step0 = (fun i j => raw22957 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22957step0 raw22957; decide +kernel
      have hl : raw22957step0Labels = raw22957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22957 raw22957Labels permutation434 hz
    mixedMoment B raw22957step0 raw22957step0Labels = mixedMoment B raw22957step1 raw22957step1Labels := by
      have hz : ∀ j, raw22957step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22957step1 = (fun i j => raw22957step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22957step1 raw22957step0; decide +kernel
      have hl : raw22957step1Labels = raw22957step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22957step0 raw22957step0Labels permutation80 hz
    mixedMoment B raw22957step1 raw22957step1Labels = mixedMoment B raw22957step2 raw22957step2Labels := by
      have ha : raw22957step2 = (fun i j => raw22957step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22957step2 raw22957step1; decide +kernel
      have hl : raw22957step2Labels = raw22957step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22957step1 raw22957step1Labels permutation8 permutation3
    _ = mixedMoment B node3187 node3187Labels := by rfl

def raw22958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22958 raw22958Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw22958 raw22958Labels = mixedMoment B raw22958step0 raw22958step0Labels := by
      have hz : ∀ j, raw22958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22958step0 = (fun i j => raw22958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22958step0 raw22958; decide +kernel
      have hl : raw22958step0Labels = raw22958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22958 raw22958Labels permutation434 hz
    mixedMoment B raw22958step0 raw22958step0Labels = mixedMoment B raw22958step1 raw22958step1Labels := by
      have ha : raw22958step1 = (fun i j => raw22958step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22958step1 raw22958step0; decide +kernel
      have hl : raw22958step1Labels = raw22958step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22958step0 raw22958step0Labels permutation38 permutation3
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw22959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22959 raw22959Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw22959 raw22959Labels = mixedMoment B raw22959step0 raw22959step0Labels := by
      have hz : ∀ j, raw22959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22959step0 = (fun i j => raw22959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22959step0 raw22959; decide +kernel
      have hl : raw22959step0Labels = raw22959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22959 raw22959Labels permutation346 hz
    mixedMoment B raw22959step0 raw22959step0Labels = mixedMoment B raw22959step1 raw22959step1Labels := by
      have ha : raw22959step1 = (fun i j => raw22959step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22959step1 raw22959step0; decide +kernel
      have hl : raw22959step1Labels = raw22959step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22959step0 raw22959step0Labels permutation38 permutation3
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw22960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22960step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw22960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22960step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw22960step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22960 raw22960Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw22960 raw22960Labels = mixedMoment B raw22960step0 raw22960step0Labels := by
      have hz : ∀ j, raw22960 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22960step0 = (fun i j => raw22960 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22960step0 raw22960; decide +kernel
      have hl : raw22960step0Labels = raw22960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22960 raw22960Labels permutation434 hz
    mixedMoment B raw22960step0 raw22960step0Labels = mixedMoment B raw22960step1 raw22960step1Labels := by
      have hz : ∀ j, raw22960step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22960step1 = (fun i j => raw22960step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22960step1 raw22960step0; decide +kernel
      have hl : raw22960step1Labels = raw22960step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22960step0 raw22960step0Labels permutation80 hz
    mixedMoment B raw22960step1 raw22960step1Labels = mixedMoment B raw22960step2 raw22960step2Labels := by
      have ha : raw22960step2 = (fun i j => raw22960step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22960step2 raw22960step1; decide +kernel
      have hl : raw22960step2Labels = raw22960step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22960step1 raw22960step1Labels permutation12 permutation6
    mixedMoment B raw22960step2 raw22960step2Labels = mixedMoment B raw22960step3 raw22960step3Labels := by
      have ha : raw22960step3 = -raw22960step2 := by apply Matrix.ext; change ∀ i j, raw22960step3 i j = -(raw22960step2 i j); unfold raw22960step3 raw22960step2; decide +kernel
      have hl : raw22960step3Labels = raw22960step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw22961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22961step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw22961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22961 raw22961Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw22961 raw22961Labels = mixedMoment B raw22961step0 raw22961step0Labels := by
      have hz : ∀ j, raw22961 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22961step0 = (fun i j => raw22961 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22961step0 raw22961; decide +kernel
      have hl : raw22961step0Labels = raw22961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22961 raw22961Labels permutation434 hz
    mixedMoment B raw22961step0 raw22961step0Labels = mixedMoment B raw22961step1 raw22961step1Labels := by
      have hz : ∀ j, raw22961step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22961step1 = (fun i j => raw22961step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22961step1 raw22961step0; decide +kernel
      have hl : raw22961step1Labels = raw22961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22961step0 raw22961step0Labels permutation80 hz
    mixedMoment B raw22961step1 raw22961step1Labels = mixedMoment B raw22961step2 raw22961step2Labels := by
      have ha : raw22961step2 = (fun i j => raw22961step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22961step2 raw22961step1; decide +kernel
      have hl : raw22961step2Labels = raw22961step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22961step1 raw22961step1Labels permutation9 permutation3
    _ = mixedMoment B node3230 node3230Labels := by rfl

def raw22962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22962step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22962 raw22962Labels = mixedMoment B node648 node648Labels := by
  calc
    mixedMoment B raw22962 raw22962Labels = mixedMoment B raw22962step0 raw22962step0Labels := by
      have hz : ∀ j, raw22962 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22962step0 = (fun i j => raw22962 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22962step0 raw22962; decide +kernel
      have hl : raw22962step0Labels = raw22962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22962 raw22962Labels permutation434 hz
    mixedMoment B raw22962step0 raw22962step0Labels = mixedMoment B raw22962step1 raw22962step1Labels := by
      have hz : ∀ j, raw22962step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22962step1 = (fun i j => raw22962step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22962step1 raw22962step0; decide +kernel
      have hl : raw22962step1Labels = raw22962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22962step0 raw22962step0Labels permutation80 hz
    mixedMoment B raw22962step1 raw22962step1Labels = mixedMoment B raw22962step2 raw22962step2Labels := by
      have ha : raw22962step2 = (fun i j => raw22962step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22962step2 raw22962step1; decide +kernel
      have hl : raw22962step2Labels = raw22962step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22962step1 raw22962step1Labels permutation8 permutation3
    _ = mixedMoment B node648 node648Labels := by rfl

def raw22963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22963 raw22963Labels = mixedMoment B node1343 node1343Labels := by
  calc
    mixedMoment B raw22963 raw22963Labels = mixedMoment B raw22963step0 raw22963step0Labels := by
      have hz : ∀ j, raw22963 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22963step0 = (fun i j => raw22963 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22963step0 raw22963; decide +kernel
      have hl : raw22963step0Labels = raw22963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22963 raw22963Labels permutation434 hz
    mixedMoment B raw22963step0 raw22963step0Labels = mixedMoment B raw22963step1 raw22963step1Labels := by
      have ha : raw22963step1 = (fun i j => raw22963step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22963step1 raw22963step0; decide +kernel
      have hl : raw22963step1Labels = raw22963step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22963step0 raw22963step0Labels permutation38 permutation3
    _ = mixedMoment B node1343 node1343Labels := by rfl

def raw22964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22964 raw22964Labels = mixedMoment B node1343 node1343Labels := by
  calc
    mixedMoment B raw22964 raw22964Labels = mixedMoment B raw22964step0 raw22964step0Labels := by
      have hz : ∀ j, raw22964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22964step0 = (fun i j => raw22964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22964step0 raw22964; decide +kernel
      have hl : raw22964step0Labels = raw22964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22964 raw22964Labels permutation346 hz
    mixedMoment B raw22964step0 raw22964step0Labels = mixedMoment B raw22964step1 raw22964step1Labels := by
      have ha : raw22964step1 = (fun i j => raw22964step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22964step1 raw22964step0; decide +kernel
      have hl : raw22964step1Labels = raw22964step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22964step0 raw22964step0Labels permutation38 permutation3
    _ = mixedMoment B node1343 node1343Labels := by rfl

def raw22965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22965step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw22965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22965 raw22965Labels = mixedMoment B node1442 node1442Labels := by
  calc
    mixedMoment B raw22965 raw22965Labels = mixedMoment B raw22965step0 raw22965step0Labels := by
      have hz : ∀ j, raw22965 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22965step0 = (fun i j => raw22965 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22965step0 raw22965; decide +kernel
      have hl : raw22965step0Labels = raw22965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22965 raw22965Labels permutation434 hz
    mixedMoment B raw22965step0 raw22965step0Labels = mixedMoment B raw22965step1 raw22965step1Labels := by
      have hz : ∀ j, raw22965step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22965step1 = (fun i j => raw22965step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22965step1 raw22965step0; decide +kernel
      have hl : raw22965step1Labels = raw22965step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22965step0 raw22965step0Labels permutation80 hz
    mixedMoment B raw22965step1 raw22965step1Labels = mixedMoment B raw22965step2 raw22965step2Labels := by
      have ha : raw22965step2 = (fun i j => raw22965step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22965step2 raw22965step1; decide +kernel
      have hl : raw22965step2Labels = raw22965step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22965step1 raw22965step1Labels permutation10 permutation3
    _ = mixedMoment B node1442 node1442Labels := by rfl

def raw22966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22966step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22966 raw22966Labels = mixedMoment B node1448 node1448Labels := by
  calc
    mixedMoment B raw22966 raw22966Labels = mixedMoment B raw22966step0 raw22966step0Labels := by
      have hz : ∀ j, raw22966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22966step0 = (fun i j => raw22966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22966step0 raw22966; decide +kernel
      have hl : raw22966step0Labels = raw22966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22966 raw22966Labels permutation434 hz
    mixedMoment B raw22966step0 raw22966step0Labels = mixedMoment B raw22966step1 raw22966step1Labels := by
      have hz : ∀ j, raw22966step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22966step1 = (fun i j => raw22966step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22966step1 raw22966step0; decide +kernel
      have hl : raw22966step1Labels = raw22966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22966step0 raw22966step0Labels permutation80 hz
    mixedMoment B raw22966step1 raw22966step1Labels = mixedMoment B raw22966step2 raw22966step2Labels := by
      have ha : raw22966step2 = (fun i j => raw22966step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22966step2 raw22966step1; decide +kernel
      have hl : raw22966step2Labels = raw22966step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22966step1 raw22966step1Labels permutation9 permutation3
    _ = mixedMoment B node1448 node1448Labels := by rfl

def raw22967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22967 raw22967Labels = mixedMoment B node631 node631Labels := by
  calc
    mixedMoment B raw22967 raw22967Labels = mixedMoment B raw22967step0 raw22967step0Labels := by
      have hz : ∀ j, raw22967 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22967step0 = (fun i j => raw22967 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22967step0 raw22967; decide +kernel
      have hl : raw22967step0Labels = raw22967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22967 raw22967Labels permutation434 hz
    mixedMoment B raw22967step0 raw22967step0Labels = mixedMoment B raw22967step1 raw22967step1Labels := by
      have ha : raw22967step1 = (fun i j => raw22967step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22967step1 raw22967step0; decide +kernel
      have hl : raw22967step1Labels = raw22967step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22967step0 raw22967step0Labels permutation32 permutation3
    _ = mixedMoment B node631 node631Labels := by rfl

def raw22968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22968 raw22968Labels = mixedMoment B node1321 node1321Labels := by
  calc
    mixedMoment B raw22968 raw22968Labels = mixedMoment B raw22968step0 raw22968step0Labels := by
      have hz : ∀ j, raw22968 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22968step0 = (fun i j => raw22968 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22968step0 raw22968; decide +kernel
      have hl : raw22968step0Labels = raw22968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22968 raw22968Labels permutation434 hz
    mixedMoment B raw22968step0 raw22968step0Labels = mixedMoment B raw22968step1 raw22968step1Labels := by
      have ha : raw22968step1 = (fun i j => raw22968step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22968step1 raw22968step0; decide +kernel
      have hl : raw22968step1Labels = raw22968step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22968step0 raw22968step0Labels permutation32 permutation3
    _ = mixedMoment B node1321 node1321Labels := by rfl

def raw22969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22969 raw22969Labels = mixedMoment B node1330 node1330Labels := by
  calc
    mixedMoment B raw22969 raw22969Labels = mixedMoment B raw22969step0 raw22969step0Labels := by
      have ha : raw22969step0 = (fun i j => raw22969 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22969step0 raw22969; decide +kernel
      have hl : raw22969step0Labels = raw22969Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22969 raw22969Labels permutation200 permutation3
    _ = mixedMoment B node1330 node1330Labels := by rfl

def raw22970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22970 raw22970Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw22970 raw22970Labels = mixedMoment B raw22970step0 raw22970step0Labels := by
      have hz : ∀ j, raw22970 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22970step0 = (fun i j => raw22970 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22970step0 raw22970; decide +kernel
      have hl : raw22970step0Labels = raw22970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22970 raw22970Labels permutation434 hz
    mixedMoment B raw22970step0 raw22970step0Labels = mixedMoment B raw22970step1 raw22970step1Labels := by
      have ha : raw22970step1 = (fun i j => raw22970step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22970step1 raw22970step0; decide +kernel
      have hl : raw22970step1Labels = raw22970step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22970step0 raw22970step0Labels permutation34 permutation3
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw22971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22971 raw22971Labels = mixedMoment B node1414 node1414Labels := by
  calc
    mixedMoment B raw22971 raw22971Labels = mixedMoment B raw22971step0 raw22971step0Labels := by
      have hz : ∀ j, raw22971 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22971step0 = (fun i j => raw22971 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22971step0 raw22971; decide +kernel
      have hl : raw22971step0Labels = raw22971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22971 raw22971Labels permutation434 hz
    mixedMoment B raw22971step0 raw22971step0Labels = mixedMoment B raw22971step1 raw22971step1Labels := by
      have ha : raw22971step1 = (fun i j => raw22971step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22971step1 raw22971step0; decide +kernel
      have hl : raw22971step1Labels = raw22971step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22971step0 raw22971step0Labels permutation33 permutation3
    _ = mixedMoment B node1414 node1414Labels := by rfl

def raw22972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22972 raw22972Labels = mixedMoment B node631 node631Labels := by
  calc
    mixedMoment B raw22972 raw22972Labels = mixedMoment B raw22972step0 raw22972step0Labels := by
      have hz : ∀ j, raw22972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22972step0 = (fun i j => raw22972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22972step0 raw22972; decide +kernel
      have hl : raw22972step0Labels = raw22972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22972 raw22972Labels permutation346 hz
    mixedMoment B raw22972step0 raw22972step0Labels = mixedMoment B raw22972step1 raw22972step1Labels := by
      have ha : raw22972step1 = (fun i j => raw22972step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22972step1 raw22972step0; decide +kernel
      have hl : raw22972step1Labels = raw22972step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22972step0 raw22972step0Labels permutation32 permutation3
    _ = mixedMoment B node631 node631Labels := by rfl

def raw22973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22973step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22973 raw22973Labels = mixedMoment B node1321 node1321Labels := by
  calc
    mixedMoment B raw22973 raw22973Labels = mixedMoment B raw22973step0 raw22973step0Labels := by
      have hz : ∀ j, raw22973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22973step0 = (fun i j => raw22973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22973step0 raw22973; decide +kernel
      have hl : raw22973step0Labels = raw22973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22973 raw22973Labels permutation346 hz
    mixedMoment B raw22973step0 raw22973step0Labels = mixedMoment B raw22973step1 raw22973step1Labels := by
      have ha : raw22973step1 = (fun i j => raw22973step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22973step1 raw22973step0; decide +kernel
      have hl : raw22973step1Labels = raw22973step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22973step0 raw22973step0Labels permutation32 permutation3
    _ = mixedMoment B node1321 node1321Labels := by rfl

def raw22974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22974 raw22974Labels = mixedMoment B node1330 node1330Labels := by
  calc
    mixedMoment B raw22974 raw22974Labels = mixedMoment B raw22974step0 raw22974step0Labels := by
      have ha : raw22974step0 = (fun i j => raw22974 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22974step0 raw22974; decide +kernel
      have hl : raw22974step0Labels = raw22974Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22974 raw22974Labels permutation176 permutation3
    _ = mixedMoment B node1330 node1330Labels := by rfl

def raw22975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22975 raw22975Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw22975 raw22975Labels = mixedMoment B raw22975step0 raw22975step0Labels := by
      have hz : ∀ j, raw22975 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22975step0 = (fun i j => raw22975 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22975step0 raw22975; decide +kernel
      have hl : raw22975step0Labels = raw22975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22975 raw22975Labels permutation346 hz
    mixedMoment B raw22975step0 raw22975step0Labels = mixedMoment B raw22975step1 raw22975step1Labels := by
      have ha : raw22975step1 = (fun i j => raw22975step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22975step1 raw22975step0; decide +kernel
      have hl : raw22975step1Labels = raw22975step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22975step0 raw22975step0Labels permutation34 permutation3
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw22976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22976 raw22976Labels = mixedMoment B node1414 node1414Labels := by
  calc
    mixedMoment B raw22976 raw22976Labels = mixedMoment B raw22976step0 raw22976step0Labels := by
      have hz : ∀ j, raw22976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22976step0 = (fun i j => raw22976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22976step0 raw22976; decide +kernel
      have hl : raw22976step0Labels = raw22976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22976 raw22976Labels permutation346 hz
    mixedMoment B raw22976step0 raw22976step0Labels = mixedMoment B raw22976step1 raw22976step1Labels := by
      have ha : raw22976step1 = (fun i j => raw22976step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22976step1 raw22976step0; decide +kernel
      have hl : raw22976step1Labels = raw22976step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22976step0 raw22976step0Labels permutation33 permutation3
    _ = mixedMoment B node1414 node1414Labels := by rfl

def raw22977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw22977step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22977 raw22977Labels = mixedMoment B node636 node636Labels := by
  calc
    mixedMoment B raw22977 raw22977Labels = mixedMoment B raw22977step0 raw22977step0Labels := by
      have hz : ∀ j, raw22977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22977step0 = (fun i j => raw22977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22977step0 raw22977; decide +kernel
      have hl : raw22977step0Labels = raw22977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22977 raw22977Labels permutation434 hz
    mixedMoment B raw22977step0 raw22977step0Labels = mixedMoment B raw22977step1 raw22977step1Labels := by
      have hz : ∀ j, raw22977step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22977step1 = (fun i j => raw22977step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22977step1 raw22977step0; decide +kernel
      have hl : raw22977step1Labels = raw22977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22977step0 raw22977step0Labels permutation80 hz
    mixedMoment B raw22977step1 raw22977step1Labels = mixedMoment B raw22977step2 raw22977step2Labels := by
      have ha : raw22977step2 = (fun i j => raw22977step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22977step2 raw22977step1; decide +kernel
      have hl : raw22977step2Labels = raw22977step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22977step1 raw22977step1Labels permutation9 permutation3
    _ = mixedMoment B node636 node636Labels := by rfl

def raw22978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw22978step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22978step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw22978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22978 raw22978Labels = mixedMoment B node1325 node1325Labels := by
  calc
    mixedMoment B raw22978 raw22978Labels = mixedMoment B raw22978step0 raw22978step0Labels := by
      have hz : ∀ j, raw22978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22978step0 = (fun i j => raw22978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22978step0 raw22978; decide +kernel
      have hl : raw22978step0Labels = raw22978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22978 raw22978Labels permutation434 hz
    mixedMoment B raw22978step0 raw22978step0Labels = mixedMoment B raw22978step1 raw22978step1Labels := by
      have hz : ∀ j, raw22978step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22978step1 = (fun i j => raw22978step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22978step1 raw22978step0; decide +kernel
      have hl : raw22978step1Labels = raw22978step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22978step0 raw22978step0Labels permutation80 hz
    mixedMoment B raw22978step1 raw22978step1Labels = mixedMoment B raw22978step2 raw22978step2Labels := by
      have ha : raw22978step2 = (fun i j => raw22978step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22978step2 raw22978step1; decide +kernel
      have hl : raw22978step2Labels = raw22978step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22978step1 raw22978step1Labels permutation9 permutation3
    _ = mixedMoment B node1325 node1325Labels := by rfl

def raw22979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22979 raw22979Labels = mixedMoment B node1334 node1334Labels := by
  calc
    mixedMoment B raw22979 raw22979Labels = mixedMoment B raw22979step0 raw22979step0Labels := by
      have hz : ∀ j, raw22979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22979step0 = (fun i j => raw22979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22979step0 raw22979; decide +kernel
      have hl : raw22979step0Labels = raw22979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22979 raw22979Labels permutation434 hz
    mixedMoment B raw22979step0 raw22979step0Labels = mixedMoment B raw22979step1 raw22979step1Labels := by
      have ha : raw22979step1 = (fun i j => raw22979step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22979step1 raw22979step0; decide +kernel
      have hl : raw22979step1Labels = raw22979step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22979step0 raw22979step0Labels permutation39 permutation3
    _ = mixedMoment B node1334 node1334Labels := by rfl

def raw22980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw22980step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22980 raw22980Labels = mixedMoment B node1334 node1334Labels := by
  calc
    mixedMoment B raw22980 raw22980Labels = mixedMoment B raw22980step0 raw22980step0Labels := by
      have hz : ∀ j, raw22980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22980step0 = (fun i j => raw22980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22980step0 raw22980; decide +kernel
      have hl : raw22980step0Labels = raw22980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22980 raw22980Labels permutation346 hz
    mixedMoment B raw22980step0 raw22980step0Labels = mixedMoment B raw22980step1 raw22980step1Labels := by
      have ha : raw22980step1 = (fun i j => raw22980step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22980step1 raw22980step0; decide +kernel
      have hl : raw22980step1Labels = raw22980step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22980step0 raw22980step0Labels permutation39 permutation3
    _ = mixedMoment B node1334 node1334Labels := by rfl

def raw22981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw22981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw22981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw22981step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw22981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22981 raw22981Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw22981 raw22981Labels = mixedMoment B raw22981step0 raw22981step0Labels := by
      have hz : ∀ j, raw22981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22981step0 = (fun i j => raw22981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22981step0 raw22981; decide +kernel
      have hl : raw22981step0Labels = raw22981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22981 raw22981Labels permutation434 hz
    mixedMoment B raw22981step0 raw22981step0Labels = mixedMoment B raw22981step1 raw22981step1Labels := by
      have hz : ∀ j, raw22981step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22981step1 = (fun i j => raw22981step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22981step1 raw22981step0; decide +kernel
      have hl : raw22981step1Labels = raw22981step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22981step0 raw22981step0Labels permutation80 hz
    mixedMoment B raw22981step1 raw22981step1Labels = mixedMoment B raw22981step2 raw22981step2Labels := by
      have ha : raw22981step2 = (fun i j => raw22981step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22981step2 raw22981step1; decide +kernel
      have hl : raw22981step2Labels = raw22981step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22981step1 raw22981step1Labels permutation9 permutation3
    _ = mixedMoment B node1416 node1416Labels := by rfl

def raw22982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22982step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22982 raw22982Labels = mixedMoment B node634 node634Labels := by
  calc
    mixedMoment B raw22982 raw22982Labels = mixedMoment B raw22982step0 raw22982step0Labels := by
      have hz : ∀ j, raw22982 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22982step0 = (fun i j => raw22982 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22982step0 raw22982; decide +kernel
      have hl : raw22982step0Labels = raw22982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22982 raw22982Labels permutation434 hz
    mixedMoment B raw22982step0 raw22982step0Labels = mixedMoment B raw22982step1 raw22982step1Labels := by
      have hz : ∀ j, raw22982step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22982step1 = (fun i j => raw22982step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22982step1 raw22982step0; decide +kernel
      have hl : raw22982step1Labels = raw22982step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22982step0 raw22982step0Labels permutation80 hz
    mixedMoment B raw22982step1 raw22982step1Labels = mixedMoment B raw22982step2 raw22982step2Labels := by
      have ha : raw22982step2 = (fun i j => raw22982step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22982step2 raw22982step1; decide +kernel
      have hl : raw22982step2Labels = raw22982step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22982step1 raw22982step1Labels permutation8 permutation3
    _ = mixedMoment B node634 node634Labels := by rfl

def raw22983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22983step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22983step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw22983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22983 raw22983Labels = mixedMoment B node1323 node1323Labels := by
  calc
    mixedMoment B raw22983 raw22983Labels = mixedMoment B raw22983step0 raw22983step0Labels := by
      have hz : ∀ j, raw22983 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22983step0 = (fun i j => raw22983 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22983step0 raw22983; decide +kernel
      have hl : raw22983step0Labels = raw22983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22983 raw22983Labels permutation434 hz
    mixedMoment B raw22983step0 raw22983step0Labels = mixedMoment B raw22983step1 raw22983step1Labels := by
      have hz : ∀ j, raw22983step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22983step1 = (fun i j => raw22983step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22983step1 raw22983step0; decide +kernel
      have hl : raw22983step1Labels = raw22983step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22983step0 raw22983step0Labels permutation80 hz
    mixedMoment B raw22983step1 raw22983step1Labels = mixedMoment B raw22983step2 raw22983step2Labels := by
      have ha : raw22983step2 = (fun i j => raw22983step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22983step2 raw22983step1; decide +kernel
      have hl : raw22983step2Labels = raw22983step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22983step1 raw22983step1Labels permutation8 permutation3
    _ = mixedMoment B node1323 node1323Labels := by rfl

def raw22984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22984step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22984 raw22984Labels = mixedMoment B node1332 node1332Labels := by
  calc
    mixedMoment B raw22984 raw22984Labels = mixedMoment B raw22984step0 raw22984step0Labels := by
      have hz : ∀ j, raw22984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22984step0 = (fun i j => raw22984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22984step0 raw22984; decide +kernel
      have hl : raw22984step0Labels = raw22984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22984 raw22984Labels permutation434 hz
    mixedMoment B raw22984step0 raw22984step0Labels = mixedMoment B raw22984step1 raw22984step1Labels := by
      have ha : raw22984step1 = (fun i j => raw22984step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22984step1 raw22984step0; decide +kernel
      have hl : raw22984step1Labels = raw22984step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22984step0 raw22984step0Labels permutation38 permutation3
    _ = mixedMoment B node1332 node1332Labels := by rfl

def raw22985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw22985step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22985 raw22985Labels = mixedMoment B node1332 node1332Labels := by
  calc
    mixedMoment B raw22985 raw22985Labels = mixedMoment B raw22985step0 raw22985step0Labels := by
      have hz : ∀ j, raw22985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22985step0 = (fun i j => raw22985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22985step0 raw22985; decide +kernel
      have hl : raw22985step0Labels = raw22985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22985 raw22985Labels permutation346 hz
    mixedMoment B raw22985step0 raw22985step0Labels = mixedMoment B raw22985step1 raw22985step1Labels := by
      have ha : raw22985step1 = (fun i j => raw22985step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22985step1 raw22985step0; decide +kernel
      have hl : raw22985step1Labels = raw22985step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22985step0 raw22985step0Labels permutation38 permutation3
    _ = mixedMoment B node1332 node1332Labels := by rfl

def raw22986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw22986step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw22986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22986 raw22986Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw22986 raw22986Labels = mixedMoment B raw22986step0 raw22986step0Labels := by
      have hz : ∀ j, raw22986 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22986step0 = (fun i j => raw22986 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22986step0 raw22986; decide +kernel
      have hl : raw22986step0Labels = raw22986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22986 raw22986Labels permutation434 hz
    mixedMoment B raw22986step0 raw22986step0Labels = mixedMoment B raw22986step1 raw22986step1Labels := by
      have hz : ∀ j, raw22986step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22986step1 = (fun i j => raw22986step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22986step1 raw22986step0; decide +kernel
      have hl : raw22986step1Labels = raw22986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22986step0 raw22986step0Labels permutation80 hz
    mixedMoment B raw22986step1 raw22986step1Labels = mixedMoment B raw22986step2 raw22986step2Labels := by
      have ha : raw22986step2 = (fun i j => raw22986step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22986step2 raw22986step1; decide +kernel
      have hl : raw22986step2Labels = raw22986step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22986step1 raw22986step1Labels permutation8 permutation3
    _ = mixedMoment B node1408 node1408Labels := by rfl

def raw22987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22987step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw22987step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22987step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22987step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22987step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22987step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22987 raw22987Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw22987 raw22987Labels = mixedMoment B raw22987step0 raw22987step0Labels := by
      have hz : ∀ j, raw22987 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22987step0 = (fun i j => raw22987 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22987step0 raw22987; decide +kernel
      have hl : raw22987step0Labels = raw22987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22987 raw22987Labels permutation434 hz
    mixedMoment B raw22987step0 raw22987step0Labels = mixedMoment B raw22987step1 raw22987step1Labels := by
      have hz : ∀ j, raw22987step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22987step1 = (fun i j => raw22987step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22987step1 raw22987step0; decide +kernel
      have hl : raw22987step1Labels = raw22987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22987step0 raw22987step0Labels permutation80 hz
    mixedMoment B raw22987step1 raw22987step1Labels = mixedMoment B raw22987step2 raw22987step2Labels := by
      have ha : raw22987step2 = (fun i j => raw22987step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22987step2 raw22987step1; decide +kernel
      have hl : raw22987step2Labels = raw22987step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22987step1 raw22987step1Labels permutation12 permutation7
    mixedMoment B raw22987step2 raw22987step2Labels = mixedMoment B raw22987step3 raw22987step3Labels := by
      have ha : raw22987step3 = -raw22987step2 := by apply Matrix.ext; change ∀ i j, raw22987step3 i j = -(raw22987step2 i j); unfold raw22987step3 raw22987step2; decide +kernel
      have hl : raw22987step3Labels = raw22987step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22987step3 raw22987step3Labels = mixedMoment B raw22987step4 raw22987step4Labels := by
      have ha : raw22987step4 = raw22987step3 := by apply Matrix.ext; unfold raw22987step4 raw22987step3; decide +kernel
      have hl : raw22987step3Labels = labelEmbedding1 ∘ raw22987step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22987step3 raw22987step3Labels raw22987step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw22988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22988step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22988step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22988step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22988 raw22988Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw22988 raw22988Labels = mixedMoment B raw22988step0 raw22988step0Labels := by
      have hz : ∀ j, raw22988 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22988step0 = (fun i j => raw22988 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22988step0 raw22988; decide +kernel
      have hl : raw22988step0Labels = raw22988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22988 raw22988Labels permutation434 hz
    mixedMoment B raw22988step0 raw22988step0Labels = mixedMoment B raw22988step1 raw22988step1Labels := by
      have ha : raw22988step1 = (fun i j => raw22988step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22988step1 raw22988step0; decide +kernel
      have hl : raw22988step1Labels = raw22988step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22988step0 raw22988step0Labels permutation42 permutation7
    mixedMoment B raw22988step1 raw22988step1Labels = mixedMoment B raw22988step2 raw22988step2Labels := by
      have ha : raw22988step2 = -raw22988step1 := by apply Matrix.ext; change ∀ i j, raw22988step2 i j = -(raw22988step1 i j); unfold raw22988step2 raw22988step1; decide +kernel
      have hl : raw22988step2Labels = raw22988step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22988step2 raw22988step2Labels = mixedMoment B raw22988step3 raw22988step3Labels := by
      have ha : raw22988step3 = raw22988step2 := by apply Matrix.ext; unfold raw22988step3 raw22988step2; decide +kernel
      have hl : raw22988step2Labels = labelEmbedding1 ∘ raw22988step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22988step2 raw22988step2Labels raw22988step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw22989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22989step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22989step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22989 raw22989Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw22989 raw22989Labels = mixedMoment B raw22989step0 raw22989step0Labels := by
      have hz : ∀ j, raw22989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22989step0 = (fun i j => raw22989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22989step0 raw22989; decide +kernel
      have hl : raw22989step0Labels = raw22989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22989 raw22989Labels permutation346 hz
    mixedMoment B raw22989step0 raw22989step0Labels = mixedMoment B raw22989step1 raw22989step1Labels := by
      have ha : raw22989step1 = (fun i j => raw22989step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22989step1 raw22989step0; decide +kernel
      have hl : raw22989step1Labels = raw22989step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22989step0 raw22989step0Labels permutation42 permutation7
    mixedMoment B raw22989step1 raw22989step1Labels = mixedMoment B raw22989step2 raw22989step2Labels := by
      have ha : raw22989step2 = -raw22989step1 := by apply Matrix.ext; change ∀ i j, raw22989step2 i j = -(raw22989step1 i j); unfold raw22989step2 raw22989step1; decide +kernel
      have hl : raw22989step2Labels = raw22989step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22989step2 raw22989step2Labels = mixedMoment B raw22989step3 raw22989step3Labels := by
      have ha : raw22989step3 = raw22989step2 := by apply Matrix.ext; unfold raw22989step3 raw22989step2; decide +kernel
      have hl : raw22989step2Labels = labelEmbedding1 ∘ raw22989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22989step2 raw22989step2Labels raw22989step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw22990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22990step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw22990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22990step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw22990step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22990step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw22990step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22990 raw22990Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw22990 raw22990Labels = mixedMoment B raw22990step0 raw22990step0Labels := by
      have hz : ∀ j, raw22990 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22990step0 = (fun i j => raw22990 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22990step0 raw22990; decide +kernel
      have hl : raw22990step0Labels = raw22990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22990 raw22990Labels permutation434 hz
    mixedMoment B raw22990step0 raw22990step0Labels = mixedMoment B raw22990step1 raw22990step1Labels := by
      have hz : ∀ j, raw22990step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22990step1 = (fun i j => raw22990step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22990step1 raw22990step0; decide +kernel
      have hl : raw22990step1Labels = raw22990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22990step0 raw22990step0Labels permutation80 hz
    mixedMoment B raw22990step1 raw22990step1Labels = mixedMoment B raw22990step2 raw22990step2Labels := by
      have ha : raw22990step2 = (fun i j => raw22990step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22990step2 raw22990step1; decide +kernel
      have hl : raw22990step2Labels = raw22990step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22990step1 raw22990step1Labels permutation12 permutation7
    mixedMoment B raw22990step2 raw22990step2Labels = mixedMoment B raw22990step3 raw22990step3Labels := by
      have ha : raw22990step3 = -raw22990step2 := by apply Matrix.ext; change ∀ i j, raw22990step3 i j = -(raw22990step2 i j); unfold raw22990step3 raw22990step2; decide +kernel
      have hl : raw22990step3Labels = raw22990step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22990step3 raw22990step3Labels = mixedMoment B raw22990step4 raw22990step4Labels := by
      have ha : raw22990step4 = raw22990step3 := by apply Matrix.ext; unfold raw22990step4 raw22990step3; decide +kernel
      have hl : raw22990step3Labels = labelEmbedding1 ∘ raw22990step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22990step3 raw22990step3Labels raw22990step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw22991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22991step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22991step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw22991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22991step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22991step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22991step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22991step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22991 raw22991Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw22991 raw22991Labels = mixedMoment B raw22991step0 raw22991step0Labels := by
      have hz : ∀ j, raw22991 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22991step0 = (fun i j => raw22991 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22991step0 raw22991; decide +kernel
      have hl : raw22991step0Labels = raw22991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22991 raw22991Labels permutation434 hz
    mixedMoment B raw22991step0 raw22991step0Labels = mixedMoment B raw22991step1 raw22991step1Labels := by
      have hz : ∀ j, raw22991step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22991step1 = (fun i j => raw22991step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22991step1 raw22991step0; decide +kernel
      have hl : raw22991step1Labels = raw22991step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22991step0 raw22991step0Labels permutation80 hz
    mixedMoment B raw22991step1 raw22991step1Labels = mixedMoment B raw22991step2 raw22991step2Labels := by
      have ha : raw22991step2 = (fun i j => raw22991step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22991step2 raw22991step1; decide +kernel
      have hl : raw22991step2Labels = raw22991step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22991step1 raw22991step1Labels permutation12 permutation7
    mixedMoment B raw22991step2 raw22991step2Labels = mixedMoment B raw22991step3 raw22991step3Labels := by
      have ha : raw22991step3 = -raw22991step2 := by apply Matrix.ext; change ∀ i j, raw22991step3 i j = -(raw22991step2 i j); unfold raw22991step3 raw22991step2; decide +kernel
      have hl : raw22991step3Labels = raw22991step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22991step3 raw22991step3Labels = mixedMoment B raw22991step4 raw22991step4Labels := by
      have ha : raw22991step4 = raw22991step3 := by apply Matrix.ext; unfold raw22991step4 raw22991step3; decide +kernel
      have hl : raw22991step3Labels = labelEmbedding1 ∘ raw22991step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22991step3 raw22991step3Labels raw22991step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw22992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22992step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw22992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22992step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22992step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22992step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22992 raw22992Labels = mixedMoment B node1525 node1525Labels := by
  calc
    mixedMoment B raw22992 raw22992Labels = mixedMoment B raw22992step0 raw22992step0Labels := by
      have hz : ∀ j, raw22992 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22992step0 = (fun i j => raw22992 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22992step0 raw22992; decide +kernel
      have hl : raw22992step0Labels = raw22992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22992 raw22992Labels permutation434 hz
    mixedMoment B raw22992step0 raw22992step0Labels = mixedMoment B raw22992step1 raw22992step1Labels := by
      have hz : ∀ j, raw22992step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22992step1 = (fun i j => raw22992step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22992step1 raw22992step0; decide +kernel
      have hl : raw22992step1Labels = raw22992step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22992step0 raw22992step0Labels permutation80 hz
    mixedMoment B raw22992step1 raw22992step1Labels = mixedMoment B raw22992step2 raw22992step2Labels := by
      have ha : raw22992step2 = (fun i j => raw22992step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22992step2 raw22992step1; decide +kernel
      have hl : raw22992step2Labels = raw22992step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22992step1 raw22992step1Labels permutation12 permutation7
    mixedMoment B raw22992step2 raw22992step2Labels = mixedMoment B raw22992step3 raw22992step3Labels := by
      have ha : raw22992step3 = -raw22992step2 := by apply Matrix.ext; change ∀ i j, raw22992step3 i j = -(raw22992step2 i j); unfold raw22992step3 raw22992step2; decide +kernel
      have hl : raw22992step3Labels = raw22992step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22992step3 raw22992step3Labels = mixedMoment B raw22992step4 raw22992step4Labels := by
      have ha : raw22992step4 = raw22992step3 := by apply Matrix.ext; unfold raw22992step4 raw22992step3; decide +kernel
      have hl : raw22992step3Labels = labelEmbedding1 ∘ raw22992step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22992step3 raw22992step3Labels raw22992step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1525 node1525Labels := by rfl

def raw22993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw22993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22993step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22993 raw22993Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw22993 raw22993Labels = mixedMoment B raw22993step0 raw22993step0Labels := by
      have hz : ∀ j, raw22993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22993step0 = (fun i j => raw22993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22993step0 raw22993; decide +kernel
      have hl : raw22993step0Labels = raw22993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22993 raw22993Labels permutation434 hz
    mixedMoment B raw22993step0 raw22993step0Labels = mixedMoment B raw22993step1 raw22993step1Labels := by
      have ha : raw22993step1 = (fun i j => raw22993step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22993step1 raw22993step0; decide +kernel
      have hl : raw22993step1Labels = raw22993step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22993step0 raw22993step0Labels permutation42 permutation7
    mixedMoment B raw22993step1 raw22993step1Labels = mixedMoment B raw22993step2 raw22993step2Labels := by
      have ha : raw22993step2 = -raw22993step1 := by apply Matrix.ext; change ∀ i j, raw22993step2 i j = -(raw22993step1 i j); unfold raw22993step2 raw22993step1; decide +kernel
      have hl : raw22993step2Labels = raw22993step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22993step2 raw22993step2Labels = mixedMoment B raw22993step3 raw22993step3Labels := by
      have ha : raw22993step3 = raw22993step2 := by apply Matrix.ext; unfold raw22993step3 raw22993step2; decide +kernel
      have hl : raw22993step2Labels = labelEmbedding1 ∘ raw22993step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22993step2 raw22993step2Labels raw22993step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

def raw22994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw22994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw22994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22994 raw22994Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw22994 raw22994Labels = mixedMoment B raw22994step0 raw22994step0Labels := by
      have hz : ∀ j, raw22994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22994step0 = (fun i j => raw22994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22994step0 raw22994; decide +kernel
      have hl : raw22994step0Labels = raw22994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22994 raw22994Labels permutation346 hz
    mixedMoment B raw22994step0 raw22994step0Labels = mixedMoment B raw22994step1 raw22994step1Labels := by
      have ha : raw22994step1 = (fun i j => raw22994step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22994step1 raw22994step0; decide +kernel
      have hl : raw22994step1Labels = raw22994step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22994step0 raw22994step0Labels permutation42 permutation7
    mixedMoment B raw22994step1 raw22994step1Labels = mixedMoment B raw22994step2 raw22994step2Labels := by
      have ha : raw22994step2 = -raw22994step1 := by apply Matrix.ext; change ∀ i j, raw22994step2 i j = -(raw22994step1 i j); unfold raw22994step2 raw22994step1; decide +kernel
      have hl : raw22994step2Labels = raw22994step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22994step2 raw22994step2Labels = mixedMoment B raw22994step3 raw22994step3Labels := by
      have ha : raw22994step3 = raw22994step2 := by apply Matrix.ext; unfold raw22994step3 raw22994step2; decide +kernel
      have hl : raw22994step2Labels = labelEmbedding1 ∘ raw22994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22994step2 raw22994step2Labels raw22994step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

def raw22995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22995step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22995step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw22995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22995step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22995step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22995step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22995step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22995 raw22995Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw22995 raw22995Labels = mixedMoment B raw22995step0 raw22995step0Labels := by
      have hz : ∀ j, raw22995 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22995step0 = (fun i j => raw22995 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22995step0 raw22995; decide +kernel
      have hl : raw22995step0Labels = raw22995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22995 raw22995Labels permutation434 hz
    mixedMoment B raw22995step0 raw22995step0Labels = mixedMoment B raw22995step1 raw22995step1Labels := by
      have hz : ∀ j, raw22995step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22995step1 = (fun i j => raw22995step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22995step1 raw22995step0; decide +kernel
      have hl : raw22995step1Labels = raw22995step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22995step0 raw22995step0Labels permutation80 hz
    mixedMoment B raw22995step1 raw22995step1Labels = mixedMoment B raw22995step2 raw22995step2Labels := by
      have ha : raw22995step2 = (fun i j => raw22995step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22995step2 raw22995step1; decide +kernel
      have hl : raw22995step2Labels = raw22995step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22995step1 raw22995step1Labels permutation12 permutation7
    mixedMoment B raw22995step2 raw22995step2Labels = mixedMoment B raw22995step3 raw22995step3Labels := by
      have ha : raw22995step3 = -raw22995step2 := by apply Matrix.ext; change ∀ i j, raw22995step3 i j = -(raw22995step2 i j); unfold raw22995step3 raw22995step2; decide +kernel
      have hl : raw22995step3Labels = raw22995step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22995step3 raw22995step3Labels = mixedMoment B raw22995step4 raw22995step4Labels := by
      have ha : raw22995step4 = raw22995step3 := by apply Matrix.ext; unfold raw22995step4 raw22995step3; decide +kernel
      have hl : raw22995step3Labels = labelEmbedding1 ∘ raw22995step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22995step3 raw22995step3Labels raw22995step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw22996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw22996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw22996step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw22996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22996step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22996step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22996step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22996step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22996 raw22996Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw22996 raw22996Labels = mixedMoment B raw22996step0 raw22996step0Labels := by
      have hz : ∀ j, raw22996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22996step0 = (fun i j => raw22996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22996step0 raw22996; decide +kernel
      have hl : raw22996step0Labels = raw22996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22996 raw22996Labels permutation434 hz
    mixedMoment B raw22996step0 raw22996step0Labels = mixedMoment B raw22996step1 raw22996step1Labels := by
      have hz : ∀ j, raw22996step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22996step1 = (fun i j => raw22996step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22996step1 raw22996step0; decide +kernel
      have hl : raw22996step1Labels = raw22996step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22996step0 raw22996step0Labels permutation80 hz
    mixedMoment B raw22996step1 raw22996step1Labels = mixedMoment B raw22996step2 raw22996step2Labels := by
      have ha : raw22996step2 = (fun i j => raw22996step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22996step2 raw22996step1; decide +kernel
      have hl : raw22996step2Labels = raw22996step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22996step1 raw22996step1Labels permutation12 permutation7
    mixedMoment B raw22996step2 raw22996step2Labels = mixedMoment B raw22996step3 raw22996step3Labels := by
      have ha : raw22996step3 = -raw22996step2 := by apply Matrix.ext; change ∀ i j, raw22996step3 i j = -(raw22996step2 i j); unfold raw22996step3 raw22996step2; decide +kernel
      have hl : raw22996step3Labels = raw22996step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22996step3 raw22996step3Labels = mixedMoment B raw22996step4 raw22996step4Labels := by
      have ha : raw22996step4 = raw22996step3 := by apply Matrix.ext; unfold raw22996step4 raw22996step3; decide +kernel
      have hl : raw22996step3Labels = labelEmbedding1 ∘ raw22996step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22996step3 raw22996step3Labels raw22996step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw22997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22997step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22997step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22997 raw22997Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw22997 raw22997Labels = mixedMoment B raw22997step0 raw22997step0Labels := by
      have hz : ∀ j, raw22997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22997step0 = (fun i j => raw22997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22997step0 raw22997; decide +kernel
      have hl : raw22997step0Labels = raw22997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22997 raw22997Labels permutation434 hz
    mixedMoment B raw22997step0 raw22997step0Labels = mixedMoment B raw22997step1 raw22997step1Labels := by
      have ha : raw22997step1 = (fun i j => raw22997step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22997step1 raw22997step0; decide +kernel
      have hl : raw22997step1Labels = raw22997step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22997step0 raw22997step0Labels permutation42 permutation7
    mixedMoment B raw22997step1 raw22997step1Labels = mixedMoment B raw22997step2 raw22997step2Labels := by
      have ha : raw22997step2 = -raw22997step1 := by apply Matrix.ext; change ∀ i j, raw22997step2 i j = -(raw22997step1 i j); unfold raw22997step2 raw22997step1; decide +kernel
      have hl : raw22997step2Labels = raw22997step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22997step2 raw22997step2Labels = mixedMoment B raw22997step3 raw22997step3Labels := by
      have ha : raw22997step3 = raw22997step2 := by apply Matrix.ext; unfold raw22997step3 raw22997step2; decide +kernel
      have hl : raw22997step2Labels = labelEmbedding1 ∘ raw22997step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22997step2 raw22997step2Labels raw22997step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

def raw22998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw22998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22998step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22998 raw22998Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw22998 raw22998Labels = mixedMoment B raw22998step0 raw22998step0Labels := by
      have hz : ∀ j, raw22998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22998step0 = (fun i j => raw22998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22998step0 raw22998; decide +kernel
      have hl : raw22998step0Labels = raw22998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22998 raw22998Labels permutation434 hz
    mixedMoment B raw22998step0 raw22998step0Labels = mixedMoment B raw22998step1 raw22998step1Labels := by
      have ha : raw22998step1 = (fun i j => raw22998step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22998step1 raw22998step0; decide +kernel
      have hl : raw22998step1Labels = raw22998step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22998step0 raw22998step0Labels permutation42 permutation7
    mixedMoment B raw22998step1 raw22998step1Labels = mixedMoment B raw22998step2 raw22998step2Labels := by
      have ha : raw22998step2 = -raw22998step1 := by apply Matrix.ext; change ∀ i j, raw22998step2 i j = -(raw22998step1 i j); unfold raw22998step2 raw22998step1; decide +kernel
      have hl : raw22998step2Labels = raw22998step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22998step2 raw22998step2Labels = mixedMoment B raw22998step3 raw22998step3Labels := by
      have ha : raw22998step3 = raw22998step2 := by apply Matrix.ext; unfold raw22998step3 raw22998step2; decide +kernel
      have hl : raw22998step2Labels = labelEmbedding1 ∘ raw22998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22998step2 raw22998step2Labels raw22998step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

def raw22999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22999step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22999step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22999 raw22999Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw22999 raw22999Labels = mixedMoment B raw22999step0 raw22999step0Labels := by
      have ha : raw22999step0 = (fun i j => raw22999 (permutation210 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22999step0 raw22999; decide +kernel
      have hl : raw22999step0Labels = raw22999Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22999 raw22999Labels permutation210 permutation7
    mixedMoment B raw22999step0 raw22999step0Labels = mixedMoment B raw22999step1 raw22999step1Labels := by
      have ha : raw22999step1 = -raw22999step0 := by apply Matrix.ext; change ∀ i j, raw22999step1 i j = -(raw22999step0 i j); unfold raw22999step1 raw22999step0; decide +kernel
      have hl : raw22999step1Labels = raw22999step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22999step1 raw22999step1Labels = mixedMoment B raw22999step2 raw22999step2Labels := by
      have ha : raw22999step2 = raw22999step1 := by apply Matrix.ext; unfold raw22999step2 raw22999step1; decide +kernel
      have hl : raw22999step1Labels = labelEmbedding1 ∘ raw22999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22999step1 raw22999step1Labels raw22999step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

def raw23000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw23000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23000step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23000 raw23000Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw23000 raw23000Labels = mixedMoment B raw23000step0 raw23000step0Labels := by
      have hz : ∀ j, raw23000 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23000step0 = (fun i j => raw23000 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23000step0 raw23000; decide +kernel
      have hl : raw23000step0Labels = raw23000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23000 raw23000Labels permutation434 hz
    mixedMoment B raw23000step0 raw23000step0Labels = mixedMoment B raw23000step1 raw23000step1Labels := by
      have ha : raw23000step1 = (fun i j => raw23000step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23000step1 raw23000step0; decide +kernel
      have hl : raw23000step1Labels = raw23000step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23000step0 raw23000step0Labels permutation42 permutation7
    mixedMoment B raw23000step1 raw23000step1Labels = mixedMoment B raw23000step2 raw23000step2Labels := by
      have ha : raw23000step2 = -raw23000step1 := by apply Matrix.ext; change ∀ i j, raw23000step2 i j = -(raw23000step1 i j); unfold raw23000step2 raw23000step1; decide +kernel
      have hl : raw23000step2Labels = raw23000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23000step2 raw23000step2Labels = mixedMoment B raw23000step3 raw23000step3Labels := by
      have ha : raw23000step3 = raw23000step2 := by apply Matrix.ext; unfold raw23000step3 raw23000step2; decide +kernel
      have hl : raw23000step2Labels = labelEmbedding1 ∘ raw23000step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23000step2 raw23000step2Labels raw23000step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw23001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23001step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23001step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23001 raw23001Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw23001 raw23001Labels = mixedMoment B raw23001step0 raw23001step0Labels := by
      have hz : ∀ j, raw23001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23001step0 = (fun i j => raw23001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23001step0 raw23001; decide +kernel
      have hl : raw23001step0Labels = raw23001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23001 raw23001Labels permutation434 hz
    mixedMoment B raw23001step0 raw23001step0Labels = mixedMoment B raw23001step1 raw23001step1Labels := by
      have ha : raw23001step1 = (fun i j => raw23001step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23001step1 raw23001step0; decide +kernel
      have hl : raw23001step1Labels = raw23001step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23001step0 raw23001step0Labels permutation42 permutation7
    mixedMoment B raw23001step1 raw23001step1Labels = mixedMoment B raw23001step2 raw23001step2Labels := by
      have ha : raw23001step2 = -raw23001step1 := by apply Matrix.ext; change ∀ i j, raw23001step2 i j = -(raw23001step1 i j); unfold raw23001step2 raw23001step1; decide +kernel
      have hl : raw23001step2Labels = raw23001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23001step2 raw23001step2Labels = mixedMoment B raw23001step3 raw23001step3Labels := by
      have ha : raw23001step3 = raw23001step2 := by apply Matrix.ext; unfold raw23001step3 raw23001step2; decide +kernel
      have hl : raw23001step2Labels = labelEmbedding1 ∘ raw23001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23001step2 raw23001step2Labels raw23001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw23002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw23002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw23002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23002step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw23002step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23002 raw23002Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw23002 raw23002Labels = mixedMoment B raw23002step0 raw23002step0Labels := by
      have hz : ∀ j, raw23002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23002step0 = (fun i j => raw23002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23002step0 raw23002; decide +kernel
      have hl : raw23002step0Labels = raw23002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23002 raw23002Labels permutation346 hz
    mixedMoment B raw23002step0 raw23002step0Labels = mixedMoment B raw23002step1 raw23002step1Labels := by
      have ha : raw23002step1 = (fun i j => raw23002step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23002step1 raw23002step0; decide +kernel
      have hl : raw23002step1Labels = raw23002step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23002step0 raw23002step0Labels permutation42 permutation7
    mixedMoment B raw23002step1 raw23002step1Labels = mixedMoment B raw23002step2 raw23002step2Labels := by
      have ha : raw23002step2 = -raw23002step1 := by apply Matrix.ext; change ∀ i j, raw23002step2 i j = -(raw23002step1 i j); unfold raw23002step2 raw23002step1; decide +kernel
      have hl : raw23002step2Labels = raw23002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23002step2 raw23002step2Labels = mixedMoment B raw23002step3 raw23002step3Labels := by
      have ha : raw23002step3 = raw23002step2 := by apply Matrix.ext; unfold raw23002step3 raw23002step2; decide +kernel
      have hl : raw23002step2Labels = labelEmbedding1 ∘ raw23002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23002step2 raw23002step2Labels raw23002step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

def raw23003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw23003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw23003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw23003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23003 raw23003Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw23003 raw23003Labels = mixedMoment B raw23003step0 raw23003step0Labels := by
      have hz : ∀ j, raw23003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23003step0 = (fun i j => raw23003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23003step0 raw23003; decide +kernel
      have hl : raw23003step0Labels = raw23003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23003 raw23003Labels permutation346 hz
    mixedMoment B raw23003step0 raw23003step0Labels = mixedMoment B raw23003step1 raw23003step1Labels := by
      have ha : raw23003step1 = (fun i j => raw23003step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23003step1 raw23003step0; decide +kernel
      have hl : raw23003step1Labels = raw23003step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23003step0 raw23003step0Labels permutation42 permutation7
    mixedMoment B raw23003step1 raw23003step1Labels = mixedMoment B raw23003step2 raw23003step2Labels := by
      have ha : raw23003step2 = -raw23003step1 := by apply Matrix.ext; change ∀ i j, raw23003step2 i j = -(raw23003step1 i j); unfold raw23003step2 raw23003step1; decide +kernel
      have hl : raw23003step2Labels = raw23003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23003step2 raw23003step2Labels = mixedMoment B raw23003step3 raw23003step3Labels := by
      have ha : raw23003step3 = raw23003step2 := by apply Matrix.ext; unfold raw23003step3 raw23003step2; decide +kernel
      have hl : raw23003step2Labels = labelEmbedding1 ∘ raw23003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23003step2 raw23003step2Labels raw23003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

def raw23004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw23004step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw23004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23004step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw23004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23004 raw23004Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw23004 raw23004Labels = mixedMoment B raw23004step0 raw23004step0Labels := by
      have ha : raw23004step0 = (fun i j => raw23004 (permutation186 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23004step0 raw23004; decide +kernel
      have hl : raw23004step0Labels = raw23004Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23004 raw23004Labels permutation186 permutation7
    mixedMoment B raw23004step0 raw23004step0Labels = mixedMoment B raw23004step1 raw23004step1Labels := by
      have ha : raw23004step1 = -raw23004step0 := by apply Matrix.ext; change ∀ i j, raw23004step1 i j = -(raw23004step0 i j); unfold raw23004step1 raw23004step0; decide +kernel
      have hl : raw23004step1Labels = raw23004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23004step1 raw23004step1Labels = mixedMoment B raw23004step2 raw23004step2Labels := by
      have ha : raw23004step2 = raw23004step1 := by apply Matrix.ext; unfold raw23004step2 raw23004step1; decide +kernel
      have hl : raw23004step1Labels = labelEmbedding1 ∘ raw23004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23004step1 raw23004step1Labels raw23004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

def raw23005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23005step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw23005step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23005step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23005step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23005step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23005 raw23005Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw23005 raw23005Labels = mixedMoment B raw23005step0 raw23005step0Labels := by
      have hz : ∀ j, raw23005 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23005step0 = (fun i j => raw23005 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23005step0 raw23005; decide +kernel
      have hl : raw23005step0Labels = raw23005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23005 raw23005Labels permutation346 hz
    mixedMoment B raw23005step0 raw23005step0Labels = mixedMoment B raw23005step1 raw23005step1Labels := by
      have ha : raw23005step1 = (fun i j => raw23005step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23005step1 raw23005step0; decide +kernel
      have hl : raw23005step1Labels = raw23005step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23005step0 raw23005step0Labels permutation42 permutation7
    mixedMoment B raw23005step1 raw23005step1Labels = mixedMoment B raw23005step2 raw23005step2Labels := by
      have ha : raw23005step2 = -raw23005step1 := by apply Matrix.ext; change ∀ i j, raw23005step2 i j = -(raw23005step1 i j); unfold raw23005step2 raw23005step1; decide +kernel
      have hl : raw23005step2Labels = raw23005step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23005step2 raw23005step2Labels = mixedMoment B raw23005step3 raw23005step3Labels := by
      have ha : raw23005step3 = raw23005step2 := by apply Matrix.ext; unfold raw23005step3 raw23005step2; decide +kernel
      have hl : raw23005step2Labels = labelEmbedding1 ∘ raw23005step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23005step2 raw23005step2Labels raw23005step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw23006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23006 raw23006Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw23006 raw23006Labels = mixedMoment B raw23006step0 raw23006step0Labels := by
      have hz : ∀ j, raw23006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23006step0 = (fun i j => raw23006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23006step0 raw23006; decide +kernel
      have hl : raw23006step0Labels = raw23006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23006 raw23006Labels permutation346 hz
    mixedMoment B raw23006step0 raw23006step0Labels = mixedMoment B raw23006step1 raw23006step1Labels := by
      have ha : raw23006step1 = (fun i j => raw23006step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23006step1 raw23006step0; decide +kernel
      have hl : raw23006step1Labels = raw23006step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23006step0 raw23006step0Labels permutation42 permutation7
    mixedMoment B raw23006step1 raw23006step1Labels = mixedMoment B raw23006step2 raw23006step2Labels := by
      have ha : raw23006step2 = -raw23006step1 := by apply Matrix.ext; change ∀ i j, raw23006step2 i j = -(raw23006step1 i j); unfold raw23006step2 raw23006step1; decide +kernel
      have hl : raw23006step2Labels = raw23006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23006step2 raw23006step2Labels = mixedMoment B raw23006step3 raw23006step3Labels := by
      have ha : raw23006step3 = raw23006step2 := by apply Matrix.ext; unfold raw23006step3 raw23006step2; decide +kernel
      have hl : raw23006step2Labels = labelEmbedding1 ∘ raw23006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23006step2 raw23006step2Labels raw23006step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw23007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23007step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw23007step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw23007step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23007step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23007step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23007step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23007step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23007 raw23007Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw23007 raw23007Labels = mixedMoment B raw23007step0 raw23007step0Labels := by
      have hz : ∀ j, raw23007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23007step0 = (fun i j => raw23007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23007step0 raw23007; decide +kernel
      have hl : raw23007step0Labels = raw23007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23007 raw23007Labels permutation434 hz
    mixedMoment B raw23007step0 raw23007step0Labels = mixedMoment B raw23007step1 raw23007step1Labels := by
      have hz : ∀ j, raw23007step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23007step1 = (fun i j => raw23007step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23007step1 raw23007step0; decide +kernel
      have hl : raw23007step1Labels = raw23007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23007step0 raw23007step0Labels permutation80 hz
    mixedMoment B raw23007step1 raw23007step1Labels = mixedMoment B raw23007step2 raw23007step2Labels := by
      have ha : raw23007step2 = (fun i j => raw23007step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23007step2 raw23007step1; decide +kernel
      have hl : raw23007step2Labels = raw23007step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23007step1 raw23007step1Labels permutation12 permutation7
    mixedMoment B raw23007step2 raw23007step2Labels = mixedMoment B raw23007step3 raw23007step3Labels := by
      have ha : raw23007step3 = -raw23007step2 := by apply Matrix.ext; change ∀ i j, raw23007step3 i j = -(raw23007step2 i j); unfold raw23007step3 raw23007step2; decide +kernel
      have hl : raw23007step3Labels = raw23007step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23007step3 raw23007step3Labels = mixedMoment B raw23007step4 raw23007step4Labels := by
      have ha : raw23007step4 = raw23007step3 := by apply Matrix.ext; unfold raw23007step4 raw23007step3; decide +kernel
      have hl : raw23007step3Labels = labelEmbedding1 ∘ raw23007step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23007step3 raw23007step3Labels raw23007step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1523 node1523Labels := by rfl

def raw23008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23008step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw23008step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23008step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw23008step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23008step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw23008step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23008step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw23008step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23008 raw23008Labels = mixedMoment B node1735 node1735Labels := by
  calc
    mixedMoment B raw23008 raw23008Labels = mixedMoment B raw23008step0 raw23008step0Labels := by
      have hz : ∀ j, raw23008 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23008step0 = (fun i j => raw23008 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23008step0 raw23008; decide +kernel
      have hl : raw23008step0Labels = raw23008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23008 raw23008Labels permutation434 hz
    mixedMoment B raw23008step0 raw23008step0Labels = mixedMoment B raw23008step1 raw23008step1Labels := by
      have hz : ∀ j, raw23008step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23008step1 = (fun i j => raw23008step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23008step1 raw23008step0; decide +kernel
      have hl : raw23008step1Labels = raw23008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23008step0 raw23008step0Labels permutation80 hz
    mixedMoment B raw23008step1 raw23008step1Labels = mixedMoment B raw23008step2 raw23008step2Labels := by
      have ha : raw23008step2 = (fun i j => raw23008step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23008step2 raw23008step1; decide +kernel
      have hl : raw23008step2Labels = raw23008step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23008step1 raw23008step1Labels permutation12 permutation7
    mixedMoment B raw23008step2 raw23008step2Labels = mixedMoment B raw23008step3 raw23008step3Labels := by
      have ha : raw23008step3 = -raw23008step2 := by apply Matrix.ext; change ∀ i j, raw23008step3 i j = -(raw23008step2 i j); unfold raw23008step3 raw23008step2; decide +kernel
      have hl : raw23008step3Labels = raw23008step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23008step3 raw23008step3Labels = mixedMoment B raw23008step4 raw23008step4Labels := by
      have ha : raw23008step4 = raw23008step3 := by apply Matrix.ext; unfold raw23008step4 raw23008step3; decide +kernel
      have hl : raw23008step3Labels = labelEmbedding1 ∘ raw23008step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23008step3 raw23008step3Labels raw23008step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1735 node1735Labels := by rfl

def raw23009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw23009step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23009step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23009step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23009 raw23009Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw23009 raw23009Labels = mixedMoment B raw23009step0 raw23009step0Labels := by
      have hz : ∀ j, raw23009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23009step0 = (fun i j => raw23009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23009step0 raw23009; decide +kernel
      have hl : raw23009step0Labels = raw23009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23009 raw23009Labels permutation434 hz
    mixedMoment B raw23009step0 raw23009step0Labels = mixedMoment B raw23009step1 raw23009step1Labels := by
      have ha : raw23009step1 = (fun i j => raw23009step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23009step1 raw23009step0; decide +kernel
      have hl : raw23009step1Labels = raw23009step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23009step0 raw23009step0Labels permutation42 permutation7
    mixedMoment B raw23009step1 raw23009step1Labels = mixedMoment B raw23009step2 raw23009step2Labels := by
      have ha : raw23009step2 = -raw23009step1 := by apply Matrix.ext; change ∀ i j, raw23009step2 i j = -(raw23009step1 i j); unfold raw23009step2 raw23009step1; decide +kernel
      have hl : raw23009step2Labels = raw23009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23009step2 raw23009step2Labels = mixedMoment B raw23009step3 raw23009step3Labels := by
      have ha : raw23009step3 = raw23009step2 := by apply Matrix.ext; unfold raw23009step3 raw23009step2; decide +kernel
      have hl : raw23009step2Labels = labelEmbedding1 ∘ raw23009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23009step2 raw23009step2Labels raw23009step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

def raw23010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw23010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23010step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw23010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23010 raw23010Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw23010 raw23010Labels = mixedMoment B raw23010step0 raw23010step0Labels := by
      have hz : ∀ j, raw23010 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23010step0 = (fun i j => raw23010 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23010step0 raw23010; decide +kernel
      have hl : raw23010step0Labels = raw23010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23010 raw23010Labels permutation346 hz
    mixedMoment B raw23010step0 raw23010step0Labels = mixedMoment B raw23010step1 raw23010step1Labels := by
      have ha : raw23010step1 = (fun i j => raw23010step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23010step1 raw23010step0; decide +kernel
      have hl : raw23010step1Labels = raw23010step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23010step0 raw23010step0Labels permutation42 permutation7
    mixedMoment B raw23010step1 raw23010step1Labels = mixedMoment B raw23010step2 raw23010step2Labels := by
      have ha : raw23010step2 = -raw23010step1 := by apply Matrix.ext; change ∀ i j, raw23010step2 i j = -(raw23010step1 i j); unfold raw23010step2 raw23010step1; decide +kernel
      have hl : raw23010step2Labels = raw23010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23010step2 raw23010step2Labels = mixedMoment B raw23010step3 raw23010step3Labels := by
      have ha : raw23010step3 = raw23010step2 := by apply Matrix.ext; unfold raw23010step3 raw23010step2; decide +kernel
      have hl : raw23010step2Labels = labelEmbedding1 ∘ raw23010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23010step2 raw23010step2Labels raw23010step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

def raw23011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw23011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw23011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw23011step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw23011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23011step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw23011step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23011step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw23011step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23011 raw23011Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw23011 raw23011Labels = mixedMoment B raw23011step0 raw23011step0Labels := by
      have hz : ∀ j, raw23011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23011step0 = (fun i j => raw23011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23011step0 raw23011; decide +kernel
      have hl : raw23011step0Labels = raw23011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23011 raw23011Labels permutation434 hz
    mixedMoment B raw23011step0 raw23011step0Labels = mixedMoment B raw23011step1 raw23011step1Labels := by
      have hz : ∀ j, raw23011step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23011step1 = (fun i j => raw23011step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23011step1 raw23011step0; decide +kernel
      have hl : raw23011step1Labels = raw23011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23011step0 raw23011step0Labels permutation80 hz
    mixedMoment B raw23011step1 raw23011step1Labels = mixedMoment B raw23011step2 raw23011step2Labels := by
      have ha : raw23011step2 = (fun i j => raw23011step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23011step2 raw23011step1; decide +kernel
      have hl : raw23011step2Labels = raw23011step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23011step1 raw23011step1Labels permutation12 permutation7
    mixedMoment B raw23011step2 raw23011step2Labels = mixedMoment B raw23011step3 raw23011step3Labels := by
      have ha : raw23011step3 = -raw23011step2 := by apply Matrix.ext; change ∀ i j, raw23011step3 i j = -(raw23011step2 i j); unfold raw23011step3 raw23011step2; decide +kernel
      have hl : raw23011step3Labels = raw23011step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23011step3 raw23011step3Labels = mixedMoment B raw23011step4 raw23011step4Labels := by
      have ha : raw23011step4 = raw23011step3 := by apply Matrix.ext; unfold raw23011step4 raw23011step3; decide +kernel
      have hl : raw23011step3Labels = labelEmbedding1 ∘ raw23011step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23011step3 raw23011step3Labels raw23011step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw23012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw23012step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw23012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23012step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23012step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23012step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23012step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23012 raw23012Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw23012 raw23012Labels = mixedMoment B raw23012step0 raw23012step0Labels := by
      have hz : ∀ j, raw23012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23012step0 = (fun i j => raw23012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23012step0 raw23012; decide +kernel
      have hl : raw23012step0Labels = raw23012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23012 raw23012Labels permutation434 hz
    mixedMoment B raw23012step0 raw23012step0Labels = mixedMoment B raw23012step1 raw23012step1Labels := by
      have hz : ∀ j, raw23012step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23012step1 = (fun i j => raw23012step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23012step1 raw23012step0; decide +kernel
      have hl : raw23012step1Labels = raw23012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23012step0 raw23012step0Labels permutation80 hz
    mixedMoment B raw23012step1 raw23012step1Labels = mixedMoment B raw23012step2 raw23012step2Labels := by
      have ha : raw23012step2 = (fun i j => raw23012step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23012step2 raw23012step1; decide +kernel
      have hl : raw23012step2Labels = raw23012step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23012step1 raw23012step1Labels permutation12 permutation7
    mixedMoment B raw23012step2 raw23012step2Labels = mixedMoment B raw23012step3 raw23012step3Labels := by
      have ha : raw23012step3 = -raw23012step2 := by apply Matrix.ext; change ∀ i j, raw23012step3 i j = -(raw23012step2 i j); unfold raw23012step3 raw23012step2; decide +kernel
      have hl : raw23012step3Labels = raw23012step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23012step3 raw23012step3Labels = mixedMoment B raw23012step4 raw23012step4Labels := by
      have ha : raw23012step4 = raw23012step3 := by apply Matrix.ext; unfold raw23012step4 raw23012step3; decide +kernel
      have hl : raw23012step3Labels = labelEmbedding1 ∘ raw23012step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23012step3 raw23012step3Labels raw23012step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1529 node1529Labels := by rfl

def raw23013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw23013step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-2, 0, 2]]
def raw23013step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23013step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw23013step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23013step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw23013step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23013 raw23013Labels = mixedMoment B node1743 node1743Labels := by
  calc
    mixedMoment B raw23013 raw23013Labels = mixedMoment B raw23013step0 raw23013step0Labels := by
      have hz : ∀ j, raw23013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23013step0 = (fun i j => raw23013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23013step0 raw23013; decide +kernel
      have hl : raw23013step0Labels = raw23013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23013 raw23013Labels permutation434 hz
    mixedMoment B raw23013step0 raw23013step0Labels = mixedMoment B raw23013step1 raw23013step1Labels := by
      have hz : ∀ j, raw23013step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23013step1 = (fun i j => raw23013step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23013step1 raw23013step0; decide +kernel
      have hl : raw23013step1Labels = raw23013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23013step0 raw23013step0Labels permutation80 hz
    mixedMoment B raw23013step1 raw23013step1Labels = mixedMoment B raw23013step2 raw23013step2Labels := by
      have ha : raw23013step2 = (fun i j => raw23013step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23013step2 raw23013step1; decide +kernel
      have hl : raw23013step2Labels = raw23013step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23013step1 raw23013step1Labels permutation12 permutation7
    mixedMoment B raw23013step2 raw23013step2Labels = mixedMoment B raw23013step3 raw23013step3Labels := by
      have ha : raw23013step3 = -raw23013step2 := by apply Matrix.ext; change ∀ i j, raw23013step3 i j = -(raw23013step2 i j); unfold raw23013step3 raw23013step2; decide +kernel
      have hl : raw23013step3Labels = raw23013step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23013step3 raw23013step3Labels = mixedMoment B raw23013step4 raw23013step4Labels := by
      have ha : raw23013step4 = raw23013step3 := by apply Matrix.ext; unfold raw23013step4 raw23013step3; decide +kernel
      have hl : raw23013step3Labels = labelEmbedding1 ∘ raw23013step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23013step3 raw23013step3Labels raw23013step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1743 node1743Labels := by rfl

def raw23014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw23014step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23014step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23014 raw23014Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw23014 raw23014Labels = mixedMoment B raw23014step0 raw23014step0Labels := by
      have hz : ∀ j, raw23014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23014step0 = (fun i j => raw23014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23014step0 raw23014; decide +kernel
      have hl : raw23014step0Labels = raw23014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23014 raw23014Labels permutation434 hz
    mixedMoment B raw23014step0 raw23014step0Labels = mixedMoment B raw23014step1 raw23014step1Labels := by
      have ha : raw23014step1 = (fun i j => raw23014step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23014step1 raw23014step0; decide +kernel
      have hl : raw23014step1Labels = raw23014step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23014step0 raw23014step0Labels permutation42 permutation7
    mixedMoment B raw23014step1 raw23014step1Labels = mixedMoment B raw23014step2 raw23014step2Labels := by
      have ha : raw23014step2 = -raw23014step1 := by apply Matrix.ext; change ∀ i j, raw23014step2 i j = -(raw23014step1 i j); unfold raw23014step2 raw23014step1; decide +kernel
      have hl : raw23014step2Labels = raw23014step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23014step2 raw23014step2Labels = mixedMoment B raw23014step3 raw23014step3Labels := by
      have ha : raw23014step3 = raw23014step2 := by apply Matrix.ext; unfold raw23014step3 raw23014step2; decide +kernel
      have hl : raw23014step2Labels = labelEmbedding1 ∘ raw23014step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23014step2 raw23014step2Labels raw23014step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1685 node1685Labels := by rfl

def raw23015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw23015step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23015step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23015step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw23015step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23015 raw23015Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw23015 raw23015Labels = mixedMoment B raw23015step0 raw23015step0Labels := by
      have hz : ∀ j, raw23015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23015step0 = (fun i j => raw23015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23015step0 raw23015; decide +kernel
      have hl : raw23015step0Labels = raw23015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23015 raw23015Labels permutation346 hz
    mixedMoment B raw23015step0 raw23015step0Labels = mixedMoment B raw23015step1 raw23015step1Labels := by
      have ha : raw23015step1 = (fun i j => raw23015step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23015step1 raw23015step0; decide +kernel
      have hl : raw23015step1Labels = raw23015step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23015step0 raw23015step0Labels permutation42 permutation7
    mixedMoment B raw23015step1 raw23015step1Labels = mixedMoment B raw23015step2 raw23015step2Labels := by
      have ha : raw23015step2 = -raw23015step1 := by apply Matrix.ext; change ∀ i j, raw23015step2 i j = -(raw23015step1 i j); unfold raw23015step2 raw23015step1; decide +kernel
      have hl : raw23015step2Labels = raw23015step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23015step2 raw23015step2Labels = mixedMoment B raw23015step3 raw23015step3Labels := by
      have ha : raw23015step3 = raw23015step2 := by apply Matrix.ext; unfold raw23015step3 raw23015step2; decide +kernel
      have hl : raw23015step2Labels = labelEmbedding1 ∘ raw23015step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23015step2 raw23015step2Labels raw23015step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1685 node1685Labels := by rfl

def raw23016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw23016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw23016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw23016step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw23016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw23016step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23016step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw23016step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23016 raw23016Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw23016 raw23016Labels = mixedMoment B raw23016step0 raw23016step0Labels := by
      have hz : ∀ j, raw23016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23016step0 = (fun i j => raw23016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23016step0 raw23016; decide +kernel
      have hl : raw23016step0Labels = raw23016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23016 raw23016Labels permutation434 hz
    mixedMoment B raw23016step0 raw23016step0Labels = mixedMoment B raw23016step1 raw23016step1Labels := by
      have hz : ∀ j, raw23016step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23016step1 = (fun i j => raw23016step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23016step1 raw23016step0; decide +kernel
      have hl : raw23016step1Labels = raw23016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23016step0 raw23016step0Labels permutation80 hz
    mixedMoment B raw23016step1 raw23016step1Labels = mixedMoment B raw23016step2 raw23016step2Labels := by
      have ha : raw23016step2 = (fun i j => raw23016step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23016step2 raw23016step1; decide +kernel
      have hl : raw23016step2Labels = raw23016step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23016step1 raw23016step1Labels permutation12 permutation7
    mixedMoment B raw23016step2 raw23016step2Labels = mixedMoment B raw23016step3 raw23016step3Labels := by
      have ha : raw23016step3 = -raw23016step2 := by apply Matrix.ext; change ∀ i j, raw23016step3 i j = -(raw23016step2 i j); unfold raw23016step3 raw23016step2; decide +kernel
      have hl : raw23016step3Labels = raw23016step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23016step3 raw23016step3Labels = mixedMoment B raw23016step4 raw23016step4Labels := by
      have ha : raw23016step4 = raw23016step3 := by apply Matrix.ext; unfold raw23016step4 raw23016step3; decide +kernel
      have hl : raw23016step3Labels = labelEmbedding1 ∘ raw23016step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23016step3 raw23016step3Labels raw23016step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

def raw23017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23017 raw23017Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw23017 raw23017Labels = mixedMoment B raw23017step0 raw23017step0Labels := by
      have hz : ∀ j, raw23017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23017step0 = (fun i j => raw23017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23017step0 raw23017; decide +kernel
      have hl : raw23017step0Labels = raw23017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23017 raw23017Labels permutation434 hz
    mixedMoment B raw23017step0 raw23017step0Labels = mixedMoment B raw23017step1 raw23017step1Labels := by
      have hz : ∀ j, raw23017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23017step1 = (fun i j => raw23017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23017step1 raw23017step0; decide +kernel
      have hl : raw23017step1Labels = raw23017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23017step0 raw23017step0Labels permutation80 hz
    mixedMoment B raw23017step1 raw23017step1Labels = mixedMoment B raw23017step2 raw23017step2Labels := by
      have ha : raw23017step2 = (fun i j => raw23017step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23017step2 raw23017step1; decide +kernel
      have hl : raw23017step2Labels = raw23017step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23017step1 raw23017step1Labels permutation9 permutation2
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw23018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23018step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23018 raw23018Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw23018 raw23018Labels = mixedMoment B raw23018step0 raw23018step0Labels := by
      have hz : ∀ j, raw23018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23018step0 = (fun i j => raw23018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23018step0 raw23018; decide +kernel
      have hl : raw23018step0Labels = raw23018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23018 raw23018Labels permutation434 hz
    mixedMoment B raw23018step0 raw23018step0Labels = mixedMoment B raw23018step1 raw23018step1Labels := by
      have hz : ∀ j, raw23018step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23018step1 = (fun i j => raw23018step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23018step1 raw23018step0; decide +kernel
      have hl : raw23018step1Labels = raw23018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23018step0 raw23018step0Labels permutation80 hz
    mixedMoment B raw23018step1 raw23018step1Labels = mixedMoment B raw23018step2 raw23018step2Labels := by
      have ha : raw23018step2 = (fun i j => raw23018step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23018step2 raw23018step1; decide +kernel
      have hl : raw23018step2Labels = raw23018step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23018step1 raw23018step1Labels permutation9 permutation2
    _ = mixedMoment B node613 node613Labels := by rfl

def raw23019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23019 raw23019Labels = mixedMoment B node582 node582Labels := by
  calc
    mixedMoment B raw23019 raw23019Labels = mixedMoment B raw23019step0 raw23019step0Labels := by
      have hz : ∀ j, raw23019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23019step0 = (fun i j => raw23019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23019step0 raw23019; decide +kernel
      have hl : raw23019step0Labels = raw23019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23019 raw23019Labels permutation434 hz
    mixedMoment B raw23019step0 raw23019step0Labels = mixedMoment B raw23019step1 raw23019step1Labels := by
      have ha : raw23019step1 = (fun i j => raw23019step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23019step1 raw23019step0; decide +kernel
      have hl : raw23019step1Labels = raw23019step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23019step0 raw23019step0Labels permutation33 permutation2
    _ = mixedMoment B node582 node582Labels := by rfl

def raw23020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23020 raw23020Labels = mixedMoment B node582 node582Labels := by
  calc
    mixedMoment B raw23020 raw23020Labels = mixedMoment B raw23020step0 raw23020step0Labels := by
      have hz : ∀ j, raw23020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23020step0 = (fun i j => raw23020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23020step0 raw23020; decide +kernel
      have hl : raw23020step0Labels = raw23020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23020 raw23020Labels permutation346 hz
    mixedMoment B raw23020step0 raw23020step0Labels = mixedMoment B raw23020step1 raw23020step1Labels := by
      have ha : raw23020step1 = (fun i j => raw23020step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23020step1 raw23020step0; decide +kernel
      have hl : raw23020step1Labels = raw23020step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23020step0 raw23020step0Labels permutation33 permutation2
    _ = mixedMoment B node582 node582Labels := by rfl

def raw23021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw23021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw23021step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23021 raw23021Labels = mixedMoment B node588 node588Labels := by
  calc
    mixedMoment B raw23021 raw23021Labels = mixedMoment B raw23021step0 raw23021step0Labels := by
      have hz : ∀ j, raw23021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23021step0 = (fun i j => raw23021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23021step0 raw23021; decide +kernel
      have hl : raw23021step0Labels = raw23021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23021 raw23021Labels permutation434 hz
    mixedMoment B raw23021step0 raw23021step0Labels = mixedMoment B raw23021step1 raw23021step1Labels := by
      have hz : ∀ j, raw23021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23021step1 = (fun i j => raw23021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23021step1 raw23021step0; decide +kernel
      have hl : raw23021step1Labels = raw23021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23021step0 raw23021step0Labels permutation80 hz
    mixedMoment B raw23021step1 raw23021step1Labels = mixedMoment B raw23021step2 raw23021step2Labels := by
      have ha : raw23021step2 = (fun i j => raw23021step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23021step2 raw23021step1; decide +kernel
      have hl : raw23021step2Labels = raw23021step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23021step1 raw23021step1Labels permutation9 permutation2
    _ = mixedMoment B node588 node588Labels := by rfl

def raw23022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw23022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23022 raw23022Labels = mixedMoment B node590 node590Labels := by
  calc
    mixedMoment B raw23022 raw23022Labels = mixedMoment B raw23022step0 raw23022step0Labels := by
      have hz : ∀ j, raw23022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23022step0 = (fun i j => raw23022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23022step0 raw23022; decide +kernel
      have hl : raw23022step0Labels = raw23022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23022 raw23022Labels permutation434 hz
    mixedMoment B raw23022step0 raw23022step0Labels = mixedMoment B raw23022step1 raw23022step1Labels := by
      have hz : ∀ j, raw23022step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23022step1 = (fun i j => raw23022step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23022step1 raw23022step0; decide +kernel
      have hl : raw23022step1Labels = raw23022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23022step0 raw23022step0Labels permutation80 hz
    _ = mixedMoment B node590 node590Labels := by rfl

def raw23023 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2], ![0, 0]]
def raw23023Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23023step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]
def raw23023step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23023step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2]]
def raw23023step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23023step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw23023step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23023 raw23023Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23023 raw23023Labels = mixedMoment B raw23023step0 raw23023step0Labels := by
      have hz : ∀ j, raw23023 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw23023step0 = (fun i j => raw23023 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw23023step0 raw23023; decide +kernel
      have hl : raw23023step0Labels = raw23023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23023 raw23023Labels permutation590 hz
    mixedMoment B raw23023step0 raw23023step0Labels = mixedMoment B raw23023step1 raw23023step1Labels := by
      have hz : ∀ j, raw23023step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw23023step1 = (fun i j => raw23023step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw23023step1 raw23023step0; decide +kernel
      have hl : raw23023step1Labels = raw23023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23023step0 raw23023step0Labels permutation104 hz
    mixedMoment B raw23023step1 raw23023step1Labels = mixedMoment B raw23023step2 raw23023step2Labels := by
      have hz : ∀ j, raw23023step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw23023step2 = (fun i j => raw23023step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw23023step2 raw23023step1; decide +kernel
      have hl : raw23023step2Labels = raw23023step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23023step1 raw23023step1Labels permutation20 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw23024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23024 raw23024Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw23024 raw23024Labels = mixedMoment B raw23024step0 raw23024step0Labels := by
      have hz : ∀ j, raw23024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23024step0 = (fun i j => raw23024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23024step0 raw23024; decide +kernel
      have hl : raw23024step0Labels = raw23024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23024 raw23024Labels permutation434 hz
    mixedMoment B raw23024step0 raw23024step0Labels = mixedMoment B raw23024step1 raw23024step1Labels := by
      have ha : raw23024step1 = (fun i j => raw23024step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23024step1 raw23024step0; decide +kernel
      have hl : raw23024step1Labels = raw23024step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23024step0 raw23024step0Labels permutation39 permutation2
    _ = mixedMoment B node932 node932Labels := by rfl

def raw23025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23025 raw23025Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw23025 raw23025Labels = mixedMoment B raw23025step0 raw23025step0Labels := by
      have hz : ∀ j, raw23025 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23025step0 = (fun i j => raw23025 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23025step0 raw23025; decide +kernel
      have hl : raw23025step0Labels = raw23025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23025 raw23025Labels permutation346 hz
    mixedMoment B raw23025step0 raw23025step0Labels = mixedMoment B raw23025step1 raw23025step1Labels := by
      have ha : raw23025step1 = (fun i j => raw23025step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23025step1 raw23025step0; decide +kernel
      have hl : raw23025step1Labels = raw23025step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23025step0 raw23025step0Labels permutation39 permutation2
    _ = mixedMoment B node932 node932Labels := by rfl

def raw23026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23026 raw23026Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw23026 raw23026Labels = mixedMoment B raw23026step0 raw23026step0Labels := by
      have hz : ∀ j, raw23026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23026step0 = (fun i j => raw23026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23026step0 raw23026; decide +kernel
      have hl : raw23026step0Labels = raw23026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23026 raw23026Labels permutation434 hz
    mixedMoment B raw23026step0 raw23026step0Labels = mixedMoment B raw23026step1 raw23026step1Labels := by
      have hz : ∀ j, raw23026step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23026step1 = (fun i j => raw23026step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23026step1 raw23026step0; decide +kernel
      have hl : raw23026step1Labels = raw23026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23026step0 raw23026step0Labels permutation80 hz
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw23027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw23027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23027 raw23027Labels = mixedMoment B node1082 node1082Labels := by
  calc
    mixedMoment B raw23027 raw23027Labels = mixedMoment B raw23027step0 raw23027step0Labels := by
      have hz : ∀ j, raw23027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23027step0 = (fun i j => raw23027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23027step0 raw23027; decide +kernel
      have hl : raw23027step0Labels = raw23027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23027 raw23027Labels permutation434 hz
    mixedMoment B raw23027step0 raw23027step0Labels = mixedMoment B raw23027step1 raw23027step1Labels := by
      have hz : ∀ j, raw23027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23027step1 = (fun i j => raw23027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23027step1 raw23027step0; decide +kernel
      have hl : raw23027step1Labels = raw23027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23027step0 raw23027step0Labels permutation80 hz
    mixedMoment B raw23027step1 raw23027step1Labels = mixedMoment B raw23027step2 raw23027step2Labels := by
      have ha : raw23027step2 = (fun i j => raw23027step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23027step2 raw23027step1; decide +kernel
      have hl : raw23027step2Labels = raw23027step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23027step1 raw23027step1Labels permutation12 permutation2
    _ = mixedMoment B node1082 node1082Labels := by rfl

def raw23028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw23028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23028 raw23028Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw23028 raw23028Labels = mixedMoment B raw23028step0 raw23028step0Labels := by
      have hz : ∀ j, raw23028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23028step0 = (fun i j => raw23028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23028step0 raw23028; decide +kernel
      have hl : raw23028step0Labels = raw23028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23028 raw23028Labels permutation434 hz
    mixedMoment B raw23028step0 raw23028step0Labels = mixedMoment B raw23028step1 raw23028step1Labels := by
      have hz : ∀ j, raw23028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23028step1 = (fun i j => raw23028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23028step1 raw23028step0; decide +kernel
      have hl : raw23028step1Labels = raw23028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23028step0 raw23028step0Labels permutation80 hz
    mixedMoment B raw23028step1 raw23028step1Labels = mixedMoment B raw23028step2 raw23028step2Labels := by
      have ha : raw23028step2 = (fun i j => raw23028step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23028step2 raw23028step1; decide +kernel
      have hl : raw23028step2Labels = raw23028step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23028step1 raw23028step1Labels permutation9 permutation2
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw23029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23029 raw23029Labels = mixedMoment B node946 node946Labels := by
  calc
    mixedMoment B raw23029 raw23029Labels = mixedMoment B raw23029step0 raw23029step0Labels := by
      have hz : ∀ j, raw23029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23029step0 = (fun i j => raw23029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23029step0 raw23029; decide +kernel
      have hl : raw23029step0Labels = raw23029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23029 raw23029Labels permutation434 hz
    mixedMoment B raw23029step0 raw23029step0Labels = mixedMoment B raw23029step1 raw23029step1Labels := by
      have ha : raw23029step1 = (fun i j => raw23029step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23029step1 raw23029step0; decide +kernel
      have hl : raw23029step1Labels = raw23029step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23029step0 raw23029step0Labels permutation33 permutation2
    _ = mixedMoment B node946 node946Labels := by rfl

def raw23030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23030 raw23030Labels = mixedMoment B node946 node946Labels := by
  calc
    mixedMoment B raw23030 raw23030Labels = mixedMoment B raw23030step0 raw23030step0Labels := by
      have hz : ∀ j, raw23030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23030step0 = (fun i j => raw23030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23030step0 raw23030; decide +kernel
      have hl : raw23030step0Labels = raw23030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23030 raw23030Labels permutation346 hz
    mixedMoment B raw23030step0 raw23030step0Labels = mixedMoment B raw23030step1 raw23030step1Labels := by
      have ha : raw23030step1 = (fun i j => raw23030step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23030step1 raw23030step0; decide +kernel
      have hl : raw23030step1Labels = raw23030step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23030step0 raw23030step0Labels permutation33 permutation2
    _ = mixedMoment B node946 node946Labels := by rfl

def raw23031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw23031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw23031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23031step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw23031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23031 raw23031Labels = mixedMoment B node952 node952Labels := by
  calc
    mixedMoment B raw23031 raw23031Labels = mixedMoment B raw23031step0 raw23031step0Labels := by
      have hz : ∀ j, raw23031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23031step0 = (fun i j => raw23031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23031step0 raw23031; decide +kernel
      have hl : raw23031step0Labels = raw23031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23031 raw23031Labels permutation434 hz
    mixedMoment B raw23031step0 raw23031step0Labels = mixedMoment B raw23031step1 raw23031step1Labels := by
      have hz : ∀ j, raw23031step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23031step1 = (fun i j => raw23031step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23031step1 raw23031step0; decide +kernel
      have hl : raw23031step1Labels = raw23031step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23031step0 raw23031step0Labels permutation80 hz
    mixedMoment B raw23031step1 raw23031step1Labels = mixedMoment B raw23031step2 raw23031step2Labels := by
      have ha : raw23031step2 = (fun i j => raw23031step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23031step2 raw23031step1; decide +kernel
      have hl : raw23031step2Labels = raw23031step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23031step1 raw23031step1Labels permutation9 permutation2
    _ = mixedMoment B node952 node952Labels := by rfl

def raw23032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw23032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw23032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23032 raw23032Labels = mixedMoment B node954 node954Labels := by
  calc
    mixedMoment B raw23032 raw23032Labels = mixedMoment B raw23032step0 raw23032step0Labels := by
      have hz : ∀ j, raw23032 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23032step0 = (fun i j => raw23032 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23032step0 raw23032; decide +kernel
      have hl : raw23032step0Labels = raw23032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23032 raw23032Labels permutation434 hz
    mixedMoment B raw23032step0 raw23032step0Labels = mixedMoment B raw23032step1 raw23032step1Labels := by
      have hz : ∀ j, raw23032step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23032step1 = (fun i j => raw23032step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23032step1 raw23032step0; decide +kernel
      have hl : raw23032step1Labels = raw23032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23032step0 raw23032step0Labels permutation80 hz
    _ = mixedMoment B node954 node954Labels := by rfl

def raw23033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw23033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23033 raw23033Labels = mixedMoment B node906 node906Labels := by
  calc
    mixedMoment B raw23033 raw23033Labels = mixedMoment B raw23033step0 raw23033step0Labels := by
      have ha : raw23033step0 = (fun i j => raw23033 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23033step0 raw23033; decide +kernel
      have hl : raw23033step0Labels = raw23033Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23033 raw23033Labels permutation201 permutation2
    _ = mixedMoment B node906 node906Labels := by rfl

def raw23034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23034 raw23034Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw23034 raw23034Labels = mixedMoment B raw23034step0 raw23034step0Labels := by
      have hz : ∀ j, raw23034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23034step0 = (fun i j => raw23034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23034step0 raw23034; decide +kernel
      have hl : raw23034step0Labels = raw23034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23034 raw23034Labels permutation434 hz
    _ = mixedMoment B node1042 node1042Labels := by rfl

def raw23035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw23035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23035 raw23035Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw23035 raw23035Labels = mixedMoment B raw23035step0 raw23035step0Labels := by
      have hz : ∀ j, raw23035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23035step0 = (fun i j => raw23035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23035step0 raw23035; decide +kernel
      have hl : raw23035step0Labels = raw23035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23035 raw23035Labels permutation434 hz
    mixedMoment B raw23035step0 raw23035step0Labels = mixedMoment B raw23035step1 raw23035step1Labels := by
      have ha : raw23035step1 = (fun i j => raw23035step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23035step1 raw23035step0; decide +kernel
      have hl : raw23035step1Labels = raw23035step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23035step0 raw23035step0Labels permutation33 permutation2
    _ = mixedMoment B node1040 node1040Labels := by rfl

def raw23036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23036step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23036 raw23036Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw23036 raw23036Labels = mixedMoment B raw23036step0 raw23036step0Labels := by
      have hz : ∀ j, raw23036 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23036step0 = (fun i j => raw23036 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23036step0 raw23036; decide +kernel
      have hl : raw23036step0Labels = raw23036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23036 raw23036Labels permutation434 hz
    mixedMoment B raw23036step0 raw23036step0Labels = mixedMoment B raw23036step1 raw23036step1Labels := by
      have ha : raw23036step1 = (fun i j => raw23036step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23036step1 raw23036step0; decide +kernel
      have hl : raw23036step1Labels = raw23036step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23036step0 raw23036step0Labels permutation39 permutation3
    mixedMoment B raw23036step1 raw23036step1Labels = mixedMoment B raw23036step2 raw23036step2Labels := by
      have ha : raw23036step2 = raw23036step1 := by apply Matrix.ext; unfold raw23036step2 raw23036step1; decide +kernel
      have hl : raw23036step1Labels = labelEmbedding6 ∘ raw23036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23036step1 raw23036step1Labels raw23036step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw23037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23037step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23037 raw23037Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw23037 raw23037Labels = mixedMoment B raw23037step0 raw23037step0Labels := by
      have hz : ∀ j, raw23037 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23037step0 = (fun i j => raw23037 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23037step0 raw23037; decide +kernel
      have hl : raw23037step0Labels = raw23037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23037 raw23037Labels permutation346 hz
    mixedMoment B raw23037step0 raw23037step0Labels = mixedMoment B raw23037step1 raw23037step1Labels := by
      have ha : raw23037step1 = (fun i j => raw23037step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23037step1 raw23037step0; decide +kernel
      have hl : raw23037step1Labels = raw23037step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23037step0 raw23037step0Labels permutation39 permutation3
    mixedMoment B raw23037step1 raw23037step1Labels = mixedMoment B raw23037step2 raw23037step2Labels := by
      have ha : raw23037step2 = raw23037step1 := by apply Matrix.ext; unfold raw23037step2 raw23037step1; decide +kernel
      have hl : raw23037step1Labels = labelEmbedding6 ∘ raw23037step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23037step1 raw23037step1Labels raw23037step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw23038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23038step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23038step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23038 raw23038Labels = mixedMoment B node4132 node4132Labels := by
  calc
    mixedMoment B raw23038 raw23038Labels = mixedMoment B raw23038step0 raw23038step0Labels := by
      have hz : ∀ j, raw23038 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23038step0 = (fun i j => raw23038 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23038step0 raw23038; decide +kernel
      have hl : raw23038step0Labels = raw23038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23038 raw23038Labels permutation434 hz
    mixedMoment B raw23038step0 raw23038step0Labels = mixedMoment B raw23038step1 raw23038step1Labels := by
      have hz : ∀ j, raw23038step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23038step1 = (fun i j => raw23038step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23038step1 raw23038step0; decide +kernel
      have hl : raw23038step1Labels = raw23038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23038step0 raw23038step0Labels permutation80 hz
    mixedMoment B raw23038step1 raw23038step1Labels = mixedMoment B raw23038step2 raw23038step2Labels := by
      have ha : raw23038step2 = (fun i j => raw23038step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23038step2 raw23038step1; decide +kernel
      have hl : raw23038step2Labels = raw23038step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23038step1 raw23038step1Labels permutation9 permutation3
    mixedMoment B raw23038step2 raw23038step2Labels = mixedMoment B raw23038step3 raw23038step3Labels := by
      have ha : raw23038step3 = raw23038step2 := by apply Matrix.ext; unfold raw23038step3 raw23038step2; decide +kernel
      have hl : raw23038step2Labels = labelEmbedding6 ∘ raw23038step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23038step2 raw23038step2Labels raw23038step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4132 node4132Labels := by rfl

def raw23039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23039step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23039 raw23039Labels = mixedMoment B node4313 node4313Labels := by
  calc
    mixedMoment B raw23039 raw23039Labels = mixedMoment B raw23039step0 raw23039step0Labels := by
      have hz : ∀ j, raw23039 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23039step0 = (fun i j => raw23039 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23039step0 raw23039; decide +kernel
      have hl : raw23039step0Labels = raw23039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23039 raw23039Labels permutation434 hz
    mixedMoment B raw23039step0 raw23039step0Labels = mixedMoment B raw23039step1 raw23039step1Labels := by
      have ha : raw23039step1 = (fun i j => raw23039step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23039step1 raw23039step0; decide +kernel
      have hl : raw23039step1Labels = raw23039step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23039step0 raw23039step0Labels permutation39 permutation3
    mixedMoment B raw23039step1 raw23039step1Labels = mixedMoment B raw23039step2 raw23039step2Labels := by
      have ha : raw23039step2 = raw23039step1 := by apply Matrix.ext; unfold raw23039step2 raw23039step1; decide +kernel
      have hl : raw23039step1Labels = labelEmbedding6 ∘ raw23039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23039step1 raw23039step1Labels raw23039step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4313 node4313Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
