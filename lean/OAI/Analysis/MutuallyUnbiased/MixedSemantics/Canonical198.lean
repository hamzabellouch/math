import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw25344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw25344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25344 raw25344Labels = mixedMoment B node1004 node1004Labels := by
  calc
    mixedMoment B raw25344 raw25344Labels = mixedMoment B raw25344step0 raw25344step0Labels := by
      have hz : ∀ j, raw25344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25344step0 = (fun i j => raw25344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25344step0 raw25344; decide +kernel
      have hl : raw25344step0Labels = raw25344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25344 raw25344Labels permutation346 hz
    mixedMoment B raw25344step0 raw25344step0Labels = mixedMoment B raw25344step1 raw25344step1Labels := by
      have ha : raw25344step1 = (fun i j => raw25344step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25344step1 raw25344step0; decide +kernel
      have hl : raw25344step1Labels = raw25344step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25344step0 raw25344step0Labels permutation44 permutation2
    _ = mixedMoment B node1004 node1004Labels := by rfl

def raw25345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw25345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw25345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25345 raw25345Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw25345 raw25345Labels = mixedMoment B raw25345step0 raw25345step0Labels := by
      have hz : ∀ j, raw25345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25345step0 = (fun i j => raw25345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25345step0 raw25345; decide +kernel
      have hl : raw25345step0Labels = raw25345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25345 raw25345Labels permutation346 hz
    mixedMoment B raw25345step0 raw25345step0Labels = mixedMoment B raw25345step1 raw25345step1Labels := by
      have ha : raw25345step1 = (fun i j => raw25345step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25345step1 raw25345step0; decide +kernel
      have hl : raw25345step1Labels = raw25345step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25345step0 raw25345step0Labels permutation44 permutation2
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw25346 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25346step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25346 raw25346Labels = mixedMoment B node1645 node1645Labels := by
  calc
    mixedMoment B raw25346 raw25346Labels = mixedMoment B raw25346step0 raw25346step0Labels := by
      have hz : ∀ j, raw25346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25346step0 = (fun i j => raw25346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25346step0 raw25346; decide +kernel
      have hl : raw25346step0Labels = raw25346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25346 raw25346Labels permutation346 hz
    mixedMoment B raw25346step0 raw25346step0Labels = mixedMoment B raw25346step1 raw25346step1Labels := by
      have ha : raw25346step1 = (fun i j => raw25346step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25346step1 raw25346step0; decide +kernel
      have hl : raw25346step1Labels = raw25346step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25346step0 raw25346step0Labels permutation44 permutation4
    mixedMoment B raw25346step1 raw25346step1Labels = mixedMoment B raw25346step2 raw25346step2Labels := by
      have ha : raw25346step2 = -raw25346step1 := by apply Matrix.ext; change ∀ i j, raw25346step2 i j = -(raw25346step1 i j); unfold raw25346step2 raw25346step1; decide +kernel
      have hl : raw25346step2Labels = raw25346step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1645 node1645Labels := by rfl

def raw25347 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw25347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25347step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25347 raw25347Labels = mixedMoment B node738 node738Labels := by
  calc
    mixedMoment B raw25347 raw25347Labels = mixedMoment B raw25347step0 raw25347step0Labels := by
      have hz : ∀ j, raw25347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25347step0 = (fun i j => raw25347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25347step0 raw25347; decide +kernel
      have hl : raw25347step0Labels = raw25347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25347 raw25347Labels permutation346 hz
    mixedMoment B raw25347step0 raw25347step0Labels = mixedMoment B raw25347step1 raw25347step1Labels := by
      have ha : raw25347step1 = (fun i j => raw25347step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25347step1 raw25347step0; decide +kernel
      have hl : raw25347step1Labels = raw25347step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25347step0 raw25347step0Labels permutation46 permutation4
    mixedMoment B raw25347step1 raw25347step1Labels = mixedMoment B raw25347step2 raw25347step2Labels := by
      have ha : raw25347step2 = -raw25347step1 := by apply Matrix.ext; change ∀ i j, raw25347step2 i j = -(raw25347step1 i j); unfold raw25347step2 raw25347step1; decide +kernel
      have hl : raw25347step2Labels = raw25347step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node738 node738Labels := by rfl

def raw25348 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25348 raw25348Labels = mixedMoment B node730 node730Labels := by
  calc
    mixedMoment B raw25348 raw25348Labels = mixedMoment B raw25348step0 raw25348step0Labels := by
      have ha : raw25348step0 = (fun i j => raw25348 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25348step0 raw25348; decide +kernel
      have hl : raw25348step0Labels = raw25348Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25348 raw25348Labels permutation224 permutation4
    mixedMoment B raw25348step0 raw25348step0Labels = mixedMoment B raw25348step1 raw25348step1Labels := by
      have ha : raw25348step1 = -raw25348step0 := by apply Matrix.ext; change ∀ i j, raw25348step1 i j = -(raw25348step0 i j); unfold raw25348step1 raw25348step0; decide +kernel
      have hl : raw25348step1Labels = raw25348step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node730 node730Labels := by rfl

def raw25349 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw25349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25349 raw25349Labels = mixedMoment B node734 node734Labels := by
  calc
    mixedMoment B raw25349 raw25349Labels = mixedMoment B raw25349step0 raw25349step0Labels := by
      have hz : ∀ j, raw25349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25349step0 = (fun i j => raw25349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25349step0 raw25349; decide +kernel
      have hl : raw25349step0Labels = raw25349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25349 raw25349Labels permutation346 hz
    mixedMoment B raw25349step0 raw25349step0Labels = mixedMoment B raw25349step1 raw25349step1Labels := by
      have ha : raw25349step1 = (fun i j => raw25349step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25349step1 raw25349step0; decide +kernel
      have hl : raw25349step1Labels = raw25349step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25349step0 raw25349step0Labels permutation44 permutation4
    mixedMoment B raw25349step1 raw25349step1Labels = mixedMoment B raw25349step2 raw25349step2Labels := by
      have ha : raw25349step2 = -raw25349step1 := by apply Matrix.ext; change ∀ i j, raw25349step2 i j = -(raw25349step1 i j); unfold raw25349step2 raw25349step1; decide +kernel
      have hl : raw25349step2Labels = raw25349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node734 node734Labels := by rfl

def raw25350 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25350 raw25350Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw25350 raw25350Labels = mixedMoment B raw25350step0 raw25350step0Labels := by
      have hz : ∀ j, raw25350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25350step0 = (fun i j => raw25350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25350step0 raw25350; decide +kernel
      have hl : raw25350step0Labels = raw25350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25350 raw25350Labels permutation346 hz
    mixedMoment B raw25350step0 raw25350step0Labels = mixedMoment B raw25350step1 raw25350step1Labels := by
      have ha : raw25350step1 = (fun i j => raw25350step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25350step1 raw25350step0; decide +kernel
      have hl : raw25350step1Labels = raw25350step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25350step0 raw25350step0Labels permutation44 permutation4
    mixedMoment B raw25350step1 raw25350step1Labels = mixedMoment B raw25350step2 raw25350step2Labels := by
      have ha : raw25350step2 = -raw25350step1 := by apply Matrix.ext; change ∀ i j, raw25350step2 i j = -(raw25350step1 i j); unfold raw25350step2 raw25350step1; decide +kernel
      have hl : raw25350step2Labels = raw25350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node806 node806Labels := by rfl

def raw25351 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw25351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw25351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25351 raw25351Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw25351 raw25351Labels = mixedMoment B raw25351step0 raw25351step0Labels := by
      have hz : ∀ j, raw25351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25351step0 = (fun i j => raw25351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25351step0 raw25351; decide +kernel
      have hl : raw25351step0Labels = raw25351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25351 raw25351Labels permutation346 hz
    mixedMoment B raw25351step0 raw25351step0Labels = mixedMoment B raw25351step1 raw25351step1Labels := by
      have ha : raw25351step1 = (fun i j => raw25351step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25351step1 raw25351step0; decide +kernel
      have hl : raw25351step1Labels = raw25351step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25351step0 raw25351step0Labels permutation44 permutation4
    mixedMoment B raw25351step1 raw25351step1Labels = mixedMoment B raw25351step2 raw25351step2Labels := by
      have ha : raw25351step2 = -raw25351step1 := by apply Matrix.ext; change ∀ i j, raw25351step2 i j = -(raw25351step1 i j); unfold raw25351step2 raw25351step1; decide +kernel
      have hl : raw25351step2Labels = raw25351step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node733 node733Labels := by rfl

def raw25352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25352 raw25352Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw25352 raw25352Labels = mixedMoment B raw25352step0 raw25352step0Labels := by
      have hz : ∀ j, raw25352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25352step0 = (fun i j => raw25352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25352step0 raw25352; decide +kernel
      have hl : raw25352step0Labels = raw25352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25352 raw25352Labels permutation346 hz
    mixedMoment B raw25352step0 raw25352step0Labels = mixedMoment B raw25352step1 raw25352step1Labels := by
      have ha : raw25352step1 = (fun i j => raw25352step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25352step1 raw25352step0; decide +kernel
      have hl : raw25352step1Labels = raw25352step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25352step0 raw25352step0Labels permutation40 permutation2
    _ = mixedMoment B node4172 node4172Labels := by rfl

def raw25353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25353 raw25353Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw25353 raw25353Labels = mixedMoment B raw25353step0 raw25353step0Labels := by
      have ha : raw25353step0 = (fun i j => raw25353 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25353step0 raw25353; decide +kernel
      have hl : raw25353step0Labels = raw25353Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25353 raw25353Labels permutation184 permutation2
    _ = mixedMoment B node4341 node4341Labels := by rfl

def raw25354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25354step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25354 raw25354Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw25354 raw25354Labels = mixedMoment B raw25354step0 raw25354step0Labels := by
      have hz : ∀ j, raw25354 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25354step0 = (fun i j => raw25354 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25354step0 raw25354; decide +kernel
      have hl : raw25354step0Labels = raw25354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25354 raw25354Labels permutation520 hz
    mixedMoment B raw25354step0 raw25354step0Labels = mixedMoment B raw25354step1 raw25354step1Labels := by
      have hz : ∀ j, raw25354step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25354step1 = (fun i j => raw25354step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25354step1 raw25354step0; decide +kernel
      have hl : raw25354step1Labels = raw25354step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25354step0 raw25354step0Labels permutation80 hz
    mixedMoment B raw25354step1 raw25354step1Labels = mixedMoment B raw25354step2 raw25354step2Labels := by
      have ha : raw25354step2 = (fun i j => raw25354step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25354step2 raw25354step1; decide +kernel
      have hl : raw25354step2Labels = raw25354step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25354step1 raw25354step1Labels permutation10 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw25355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25355 raw25355Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25355 raw25355Labels = mixedMoment B raw25355step0 raw25355step0Labels := by
      have hz : ∀ j, raw25355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25355step0 = (fun i j => raw25355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25355step0 raw25355; decide +kernel
      have hl : raw25355step0Labels = raw25355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25355 raw25355Labels permutation346 hz
    mixedMoment B raw25355step0 raw25355step0Labels = mixedMoment B raw25355step1 raw25355step1Labels := by
      have ha : raw25355step1 = (fun i j => raw25355step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25355step1 raw25355step0; decide +kernel
      have hl : raw25355step1Labels = raw25355step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25355step0 raw25355step0Labels permutation40 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw25356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25356 raw25356Labels = mixedMoment B node4149 node4149Labels := by
  calc
    _ = mixedMoment B node4149 node4149Labels := by rfl

def raw25357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25357 raw25357Labels = mixedMoment B node4363 node4363Labels := by
  calc
    _ = mixedMoment B node4363 node4363Labels := by rfl

def raw25358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25358 raw25358Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw25358 raw25358Labels = mixedMoment B raw25358step0 raw25358step0Labels := by
      have hz : ∀ j, raw25358 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25358step0 = (fun i j => raw25358 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25358step0 raw25358; decide +kernel
      have hl : raw25358step0Labels = raw25358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25358 raw25358Labels permutation520 hz
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw25359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25359 raw25359Labels = mixedMoment B node4455 node4455Labels := by
  calc
    _ = mixedMoment B node4455 node4455Labels := by rfl

def raw25360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25360 raw25360Labels = mixedMoment B node4154 node4154Labels := by
  calc
    mixedMoment B raw25360 raw25360Labels = mixedMoment B raw25360step0 raw25360step0Labels := by
      have hz : ∀ j, raw25360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25360step0 = (fun i j => raw25360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25360step0 raw25360; decide +kernel
      have hl : raw25360step0Labels = raw25360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25360 raw25360Labels permutation346 hz
    mixedMoment B raw25360step0 raw25360step0Labels = mixedMoment B raw25360step1 raw25360step1Labels := by
      have ha : raw25360step1 = (fun i j => raw25360step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25360step1 raw25360step0; decide +kernel
      have hl : raw25360step1Labels = raw25360step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25360step0 raw25360step0Labels permutation34 permutation2
    _ = mixedMoment B node4154 node4154Labels := by rfl

def raw25361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25361step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25361 raw25361Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw25361 raw25361Labels = mixedMoment B raw25361step0 raw25361step0Labels := by
      have hz : ∀ j, raw25361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25361step0 = (fun i j => raw25361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25361step0 raw25361; decide +kernel
      have hl : raw25361step0Labels = raw25361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25361 raw25361Labels permutation346 hz
    mixedMoment B raw25361step0 raw25361step0Labels = mixedMoment B raw25361step1 raw25361step1Labels := by
      have ha : raw25361step1 = (fun i j => raw25361step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25361step1 raw25361step0; decide +kernel
      have hl : raw25361step1Labels = raw25361step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25361step0 raw25361step0Labels permutation34 permutation2
    _ = mixedMoment B node4368 node4368Labels := by rfl

def raw25362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25362 raw25362Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw25362 raw25362Labels = mixedMoment B raw25362step0 raw25362step0Labels := by
      have ha : raw25362step0 = (fun i j => raw25362 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25362step0 raw25362; decide +kernel
      have hl : raw25362step0Labels = raw25362Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25362 raw25362Labels permutation178 permutation2
    _ = mixedMoment B node4328 node4328Labels := by rfl

def raw25363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25363step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25363 raw25363Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw25363 raw25363Labels = mixedMoment B raw25363step0 raw25363step0Labels := by
      have hz : ∀ j, raw25363 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25363step0 = (fun i j => raw25363 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25363step0 raw25363; decide +kernel
      have hl : raw25363step0Labels = raw25363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25363 raw25363Labels permutation520 hz
    mixedMoment B raw25363step0 raw25363step0Labels = mixedMoment B raw25363step1 raw25363step1Labels := by
      have hz : ∀ j, raw25363step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25363step1 = (fun i j => raw25363step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25363step1 raw25363step0; decide +kernel
      have hl : raw25363step1Labels = raw25363step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25363step0 raw25363step0Labels permutation80 hz
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw25364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25364 raw25364Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw25364 raw25364Labels = mixedMoment B raw25364step0 raw25364step0Labels := by
      have hz : ∀ j, raw25364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25364step0 = (fun i j => raw25364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25364step0 raw25364; decide +kernel
      have hl : raw25364step0Labels = raw25364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25364 raw25364Labels permutation346 hz
    mixedMoment B raw25364step0 raw25364step0Labels = mixedMoment B raw25364step1 raw25364step1Labels := by
      have ha : raw25364step1 = (fun i j => raw25364step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25364step1 raw25364step0; decide +kernel
      have hl : raw25364step1Labels = raw25364step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25364step0 raw25364step0Labels permutation35 permutation2
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw25365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25365 raw25365Labels = mixedMoment B node4154 node4154Labels := by
  calc
    mixedMoment B raw25365 raw25365Labels = mixedMoment B raw25365step0 raw25365step0Labels := by
      have hz : ∀ j, raw25365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25365step0 = (fun i j => raw25365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25365step0 raw25365; decide +kernel
      have hl : raw25365step0Labels = raw25365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25365 raw25365Labels permutation346 hz
    _ = mixedMoment B node4154 node4154Labels := by rfl

def raw25366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25366step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25366 raw25366Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw25366 raw25366Labels = mixedMoment B raw25366step0 raw25366step0Labels := by
      have hz : ∀ j, raw25366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25366step0 = (fun i j => raw25366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25366step0 raw25366; decide +kernel
      have hl : raw25366step0Labels = raw25366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25366 raw25366Labels permutation346 hz
    _ = mixedMoment B node4368 node4368Labels := by rfl

def raw25367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25367step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25367 raw25367Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw25367 raw25367Labels = mixedMoment B raw25367step0 raw25367step0Labels := by
      have ha : raw25367step0 = (fun i j => raw25367 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25367step0 raw25367; decide +kernel
      have hl : raw25367step0Labels = raw25367Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25367 raw25367Labels permutation176 permutation2
    _ = mixedMoment B node4328 node4328Labels := by rfl

def raw25368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25368step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25368step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25368 raw25368Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw25368 raw25368Labels = mixedMoment B raw25368step0 raw25368step0Labels := by
      have hz : ∀ j, raw25368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25368step0 = (fun i j => raw25368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25368step0 raw25368; decide +kernel
      have hl : raw25368step0Labels = raw25368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25368 raw25368Labels permutation346 hz
    mixedMoment B raw25368step0 raw25368step0Labels = mixedMoment B raw25368step1 raw25368step1Labels := by
      have ha : raw25368step1 = (fun i j => raw25368step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25368step1 raw25368step0; decide +kernel
      have hl : raw25368step1Labels = raw25368step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25368step0 raw25368step0Labels permutation33 permutation2
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw25369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25369 raw25369Labels = mixedMoment B node3185 node3185Labels := by
  calc
    mixedMoment B raw25369 raw25369Labels = mixedMoment B raw25369step0 raw25369step0Labels := by
      have hz : ∀ j, raw25369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25369step0 = (fun i j => raw25369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25369step0 raw25369; decide +kernel
      have hl : raw25369step0Labels = raw25369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25369 raw25369Labels permutation346 hz
    mixedMoment B raw25369step0 raw25369step0Labels = mixedMoment B raw25369step1 raw25369step1Labels := by
      have ha : raw25369step1 = (fun i j => raw25369step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25369step1 raw25369step0; decide +kernel
      have hl : raw25369step1Labels = raw25369step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25369step0 raw25369step0Labels permutation32 permutation3
    _ = mixedMoment B node3185 node3185Labels := by rfl

def raw25370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25370 raw25370Labels = mixedMoment B node3205 node3205Labels := by
  calc
    mixedMoment B raw25370 raw25370Labels = mixedMoment B raw25370step0 raw25370step0Labels := by
      have ha : raw25370step0 = (fun i j => raw25370 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25370step0 raw25370; decide +kernel
      have hl : raw25370step0Labels = raw25370Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25370 raw25370Labels permutation176 permutation3
    _ = mixedMoment B node3205 node3205Labels := by rfl

def raw25371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25371step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw25371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25371 raw25371Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw25371 raw25371Labels = mixedMoment B raw25371step0 raw25371step0Labels := by
      have hz : ∀ j, raw25371 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25371step0 = (fun i j => raw25371 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25371step0 raw25371; decide +kernel
      have hl : raw25371step0Labels = raw25371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25371 raw25371Labels permutation520 hz
    mixedMoment B raw25371step0 raw25371step0Labels = mixedMoment B raw25371step1 raw25371step1Labels := by
      have hz : ∀ j, raw25371step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25371step1 = (fun i j => raw25371step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25371step1 raw25371step0; decide +kernel
      have hl : raw25371step1Labels = raw25371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25371step0 raw25371step0Labels permutation80 hz
    mixedMoment B raw25371step1 raw25371step1Labels = mixedMoment B raw25371step2 raw25371step2Labels := by
      have ha : raw25371step2 = (fun i j => raw25371step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25371step2 raw25371step1; decide +kernel
      have hl : raw25371step2Labels = raw25371step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25371step1 raw25371step1Labels permutation8 permutation3
    _ = mixedMoment B node3230 node3230Labels := by rfl

def raw25372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25372 raw25372Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw25372 raw25372Labels = mixedMoment B raw25372step0 raw25372step0Labels := by
      have hz : ∀ j, raw25372 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25372step0 = (fun i j => raw25372 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25372step0 raw25372; decide +kernel
      have hl : raw25372step0Labels = raw25372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25372 raw25372Labels permutation346 hz
    mixedMoment B raw25372step0 raw25372step0Labels = mixedMoment B raw25372step1 raw25372step1Labels := by
      have ha : raw25372step1 = (fun i j => raw25372step0 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25372step1 raw25372step0; decide +kernel
      have hl : raw25372step1Labels = raw25372step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25372step0 raw25372step0Labels permutation40 permutation6
    mixedMoment B raw25372step1 raw25372step1Labels = mixedMoment B raw25372step2 raw25372step2Labels := by
      have ha : raw25372step2 = -raw25372step1 := by apply Matrix.ext; change ∀ i j, raw25372step2 i j = -(raw25372step1 i j); unfold raw25372step2 raw25372step1; decide +kernel
      have hl : raw25372step2Labels = raw25372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw25373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25373 raw25373Labels = mixedMoment B node646 node646Labels := by
  calc
    mixedMoment B raw25373 raw25373Labels = mixedMoment B raw25373step0 raw25373step0Labels := by
      have hz : ∀ j, raw25373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25373step0 = (fun i j => raw25373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25373step0 raw25373; decide +kernel
      have hl : raw25373step0Labels = raw25373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25373 raw25373Labels permutation346 hz
    mixedMoment B raw25373step0 raw25373step0Labels = mixedMoment B raw25373step1 raw25373step1Labels := by
      have ha : raw25373step1 = (fun i j => raw25373step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25373step1 raw25373step0; decide +kernel
      have hl : raw25373step1Labels = raw25373step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25373step0 raw25373step0Labels permutation32 permutation3
    _ = mixedMoment B node646 node646Labels := by rfl

def raw25374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25374 raw25374Labels = mixedMoment B node1341 node1341Labels := by
  calc
    mixedMoment B raw25374 raw25374Labels = mixedMoment B raw25374step0 raw25374step0Labels := by
      have ha : raw25374step0 = (fun i j => raw25374 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25374step0 raw25374; decide +kernel
      have hl : raw25374step0Labels = raw25374Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25374 raw25374Labels permutation176 permutation3
    _ = mixedMoment B node1341 node1341Labels := by rfl

def raw25375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25375 raw25375Labels = mixedMoment B node1448 node1448Labels := by
  calc
    mixedMoment B raw25375 raw25375Labels = mixedMoment B raw25375step0 raw25375step0Labels := by
      have hz : ∀ j, raw25375 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25375step0 = (fun i j => raw25375 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25375step0 raw25375; decide +kernel
      have hl : raw25375step0Labels = raw25375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25375 raw25375Labels permutation520 hz
    mixedMoment B raw25375step0 raw25375step0Labels = mixedMoment B raw25375step1 raw25375step1Labels := by
      have hz : ∀ j, raw25375step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25375step1 = (fun i j => raw25375step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25375step1 raw25375step0; decide +kernel
      have hl : raw25375step1Labels = raw25375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25375step0 raw25375step0Labels permutation80 hz
    mixedMoment B raw25375step1 raw25375step1Labels = mixedMoment B raw25375step2 raw25375step2Labels := by
      have ha : raw25375step2 = (fun i j => raw25375step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25375step2 raw25375step1; decide +kernel
      have hl : raw25375step2Labels = raw25375step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25375step1 raw25375step1Labels permutation8 permutation3
    _ = mixedMoment B node1448 node1448Labels := by rfl

def raw25376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25376 raw25376Labels = mixedMoment B node1441 node1441Labels := by
  calc
    mixedMoment B raw25376 raw25376Labels = mixedMoment B raw25376step0 raw25376step0Labels := by
      have hz : ∀ j, raw25376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25376step0 = (fun i j => raw25376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25376step0 raw25376; decide +kernel
      have hl : raw25376step0Labels = raw25376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25376 raw25376Labels permutation346 hz
    mixedMoment B raw25376step0 raw25376step0Labels = mixedMoment B raw25376step1 raw25376step1Labels := by
      have ha : raw25376step1 = (fun i j => raw25376step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25376step1 raw25376step0; decide +kernel
      have hl : raw25376step1Labels = raw25376step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25376step0 raw25376step0Labels permutation50 permutation3
    _ = mixedMoment B node1441 node1441Labels := by rfl

def raw25377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25377 raw25377Labels = mixedMoment B node629 node629Labels := by
  calc
    mixedMoment B raw25377 raw25377Labels = mixedMoment B raw25377step0 raw25377step0Labels := by
      have ha : raw25377step0 = (fun i j => raw25377 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25377step0 raw25377; decide +kernel
      have hl : raw25377step0Labels = raw25377Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25377 raw25377Labels permutation152 permutation3
    _ = mixedMoment B node629 node629Labels := by rfl

def raw25378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25378 raw25378Labels = mixedMoment B node1319 node1319Labels := by
  calc
    mixedMoment B raw25378 raw25378Labels = mixedMoment B raw25378step0 raw25378step0Labels := by
      have ha : raw25378step0 = (fun i j => raw25378 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25378step0 raw25378; decide +kernel
      have hl : raw25378step0Labels = raw25378Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25378 raw25378Labels permutation152 permutation3
    _ = mixedMoment B node1319 node1319Labels := by rfl

def raw25379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25379 raw25379Labels = mixedMoment B node1414 node1414Labels := by
  calc
    mixedMoment B raw25379 raw25379Labels = mixedMoment B raw25379step0 raw25379step0Labels := by
      have hz : ∀ j, raw25379 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25379step0 = (fun i j => raw25379 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25379step0 raw25379; decide +kernel
      have hl : raw25379step0Labels = raw25379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25379 raw25379Labels permutation520 hz
    mixedMoment B raw25379step0 raw25379step0Labels = mixedMoment B raw25379step1 raw25379step1Labels := by
      have ha : raw25379step1 = (fun i j => raw25379step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25379step1 raw25379step0; decide +kernel
      have hl : raw25379step1Labels = raw25379step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25379step0 raw25379step0Labels permutation32 permutation3
    _ = mixedMoment B node1414 node1414Labels := by rfl

def raw25380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25380 raw25380Labels = mixedMoment B node1405 node1405Labels := by
  calc
    mixedMoment B raw25380 raw25380Labels = mixedMoment B raw25380step0 raw25380step0Labels := by
      have ha : raw25380step0 = (fun i j => raw25380 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25380step0 raw25380; decide +kernel
      have hl : raw25380step0Labels = raw25380Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25380 raw25380Labels permutation170 permutation3
    _ = mixedMoment B node1405 node1405Labels := by rfl

def raw25381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25381 raw25381Labels = mixedMoment B node631 node631Labels := by
  calc
    mixedMoment B raw25381 raw25381Labels = mixedMoment B raw25381step0 raw25381step0Labels := by
      have hz : ∀ j, raw25381 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25381step0 = (fun i j => raw25381 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25381step0 raw25381; decide +kernel
      have hl : raw25381step0Labels = raw25381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25381 raw25381Labels permutation346 hz
    mixedMoment B raw25381step0 raw25381step0Labels = mixedMoment B raw25381step1 raw25381step1Labels := by
      have ha : raw25381step1 = (fun i j => raw25381step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25381step1 raw25381step0; decide +kernel
      have hl : raw25381step1Labels = raw25381step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25381step0 raw25381step0Labels permutation35 permutation3
    _ = mixedMoment B node631 node631Labels := by rfl

def raw25382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25382 raw25382Labels = mixedMoment B node1321 node1321Labels := by
  calc
    mixedMoment B raw25382 raw25382Labels = mixedMoment B raw25382step0 raw25382step0Labels := by
      have hz : ∀ j, raw25382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25382step0 = (fun i j => raw25382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25382step0 raw25382; decide +kernel
      have hl : raw25382step0Labels = raw25382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25382 raw25382Labels permutation346 hz
    mixedMoment B raw25382step0 raw25382step0Labels = mixedMoment B raw25382step1 raw25382step1Labels := by
      have ha : raw25382step1 = (fun i j => raw25382step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25382step1 raw25382step0; decide +kernel
      have hl : raw25382step1Labels = raw25382step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25382step0 raw25382step0Labels permutation35 permutation3
    _ = mixedMoment B node1321 node1321Labels := by rfl

def raw25383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25383 raw25383Labels = mixedMoment B node1330 node1330Labels := by
  calc
    mixedMoment B raw25383 raw25383Labels = mixedMoment B raw25383step0 raw25383step0Labels := by
      have ha : raw25383step0 = (fun i j => raw25383 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25383step0 raw25383; decide +kernel
      have hl : raw25383step0Labels = raw25383Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25383 raw25383Labels permutation179 permutation3
    _ = mixedMoment B node1330 node1330Labels := by rfl

def raw25384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25384step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25384 raw25384Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw25384 raw25384Labels = mixedMoment B raw25384step0 raw25384step0Labels := by
      have hz : ∀ j, raw25384 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25384step0 = (fun i j => raw25384 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25384step0 raw25384; decide +kernel
      have hl : raw25384step0Labels = raw25384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25384 raw25384Labels permutation520 hz
    mixedMoment B raw25384step0 raw25384step0Labels = mixedMoment B raw25384step1 raw25384step1Labels := by
      have hz : ∀ j, raw25384step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25384step1 = (fun i j => raw25384step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25384step1 raw25384step0; decide +kernel
      have hl : raw25384step1Labels = raw25384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25384step0 raw25384step0Labels permutation80 hz
    mixedMoment B raw25384step1 raw25384step1Labels = mixedMoment B raw25384step2 raw25384step2Labels := by
      have ha : raw25384step2 = (fun i j => raw25384step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25384step2 raw25384step1; decide +kernel
      have hl : raw25384step2Labels = raw25384step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25384step1 raw25384step1Labels permutation9 permutation3
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw25385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25385 raw25385Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw25385 raw25385Labels = mixedMoment B raw25385step0 raw25385step0Labels := by
      have hz : ∀ j, raw25385 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25385step0 = (fun i j => raw25385 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25385step0 raw25385; decide +kernel
      have hl : raw25385step0Labels = raw25385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25385 raw25385Labels permutation346 hz
    mixedMoment B raw25385step0 raw25385step0Labels = mixedMoment B raw25385step1 raw25385step1Labels := by
      have ha : raw25385step1 = (fun i j => raw25385step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25385step1 raw25385step0; decide +kernel
      have hl : raw25385step1Labels = raw25385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25385step0 raw25385step0Labels permutation37 permutation3
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw25386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25386 raw25386Labels = mixedMoment B node631 node631Labels := by
  calc
    mixedMoment B raw25386 raw25386Labels = mixedMoment B raw25386step0 raw25386step0Labels := by
      have hz : ∀ j, raw25386 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25386step0 = (fun i j => raw25386 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25386step0 raw25386; decide +kernel
      have hl : raw25386step0Labels = raw25386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25386 raw25386Labels permutation346 hz
    mixedMoment B raw25386step0 raw25386step0Labels = mixedMoment B raw25386step1 raw25386step1Labels := by
      have ha : raw25386step1 = (fun i j => raw25386step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25386step1 raw25386step0; decide +kernel
      have hl : raw25386step1Labels = raw25386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25386step0 raw25386step0Labels permutation33 permutation3
    _ = mixedMoment B node631 node631Labels := by rfl

def raw25387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25387 raw25387Labels = mixedMoment B node1321 node1321Labels := by
  calc
    mixedMoment B raw25387 raw25387Labels = mixedMoment B raw25387step0 raw25387step0Labels := by
      have hz : ∀ j, raw25387 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25387step0 = (fun i j => raw25387 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25387step0 raw25387; decide +kernel
      have hl : raw25387step0Labels = raw25387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25387 raw25387Labels permutation346 hz
    mixedMoment B raw25387step0 raw25387step0Labels = mixedMoment B raw25387step1 raw25387step1Labels := by
      have ha : raw25387step1 = (fun i j => raw25387step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25387step1 raw25387step0; decide +kernel
      have hl : raw25387step1Labels = raw25387step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25387step0 raw25387step0Labels permutation33 permutation3
    _ = mixedMoment B node1321 node1321Labels := by rfl

def raw25388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25388 raw25388Labels = mixedMoment B node1330 node1330Labels := by
  calc
    mixedMoment B raw25388 raw25388Labels = mixedMoment B raw25388step0 raw25388step0Labels := by
      have ha : raw25388step0 = (fun i j => raw25388 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25388step0 raw25388; decide +kernel
      have hl : raw25388step0Labels = raw25388Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25388 raw25388Labels permutation177 permutation3
    _ = mixedMoment B node1330 node1330Labels := by rfl

def raw25389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25389step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25389step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25389 raw25389Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw25389 raw25389Labels = mixedMoment B raw25389step0 raw25389step0Labels := by
      have hz : ∀ j, raw25389 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25389step0 = (fun i j => raw25389 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25389step0 raw25389; decide +kernel
      have hl : raw25389step0Labels = raw25389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25389 raw25389Labels permutation346 hz
    mixedMoment B raw25389step0 raw25389step0Labels = mixedMoment B raw25389step1 raw25389step1Labels := by
      have ha : raw25389step1 = (fun i j => raw25389step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25389step1 raw25389step0; decide +kernel
      have hl : raw25389step1Labels = raw25389step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25389step0 raw25389step0Labels permutation36 permutation3
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw25390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw25390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw25390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25390step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw25390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25390 raw25390Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw25390 raw25390Labels = mixedMoment B raw25390step0 raw25390step0Labels := by
      have hz : ∀ j, raw25390 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw25390step0 = (fun i j => raw25390 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw25390step0 raw25390; decide +kernel
      have hl : raw25390step0Labels = raw25390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25390 raw25390Labels permutation434 hz
    mixedMoment B raw25390step0 raw25390step0Labels = mixedMoment B raw25390step1 raw25390step1Labels := by
      have hz : ∀ j, raw25390step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25390step1 = (fun i j => raw25390step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25390step1 raw25390step0; decide +kernel
      have hl : raw25390step1Labels = raw25390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25390step0 raw25390step0Labels permutation80 hz
    mixedMoment B raw25390step1 raw25390step1Labels = mixedMoment B raw25390step2 raw25390step2Labels := by
      have ha : raw25390step2 = (fun i j => raw25390step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25390step2 raw25390step1; decide +kernel
      have hl : raw25390step2Labels = raw25390step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25390step1 raw25390step1Labels permutation8 permutation3
    _ = mixedMoment B node1416 node1416Labels := by rfl

def raw25391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25391Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25391step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw25391step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25391step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25391step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25391step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25391 raw25391Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw25391 raw25391Labels = mixedMoment B raw25391step0 raw25391step0Labels := by
      have hz : ∀ j, raw25391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25391step0 = (fun i j => raw25391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25391step0 raw25391; decide +kernel
      have hl : raw25391step0Labels = raw25391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25391 raw25391Labels permutation346 hz
    mixedMoment B raw25391step0 raw25391step0Labels = mixedMoment B raw25391step1 raw25391step1Labels := by
      have ha : raw25391step1 = (fun i j => raw25391step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25391step1 raw25391step0; decide +kernel
      have hl : raw25391step1Labels = raw25391step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25391step0 raw25391step0Labels permutation40 permutation7
    mixedMoment B raw25391step1 raw25391step1Labels = mixedMoment B raw25391step2 raw25391step2Labels := by
      have ha : raw25391step2 = -raw25391step1 := by apply Matrix.ext; change ∀ i j, raw25391step2 i j = -(raw25391step1 i j); unfold raw25391step2 raw25391step1; decide +kernel
      have hl : raw25391step2Labels = raw25391step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25391step2 raw25391step2Labels = mixedMoment B raw25391step3 raw25391step3Labels := by
      have ha : raw25391step3 = raw25391step2 := by apply Matrix.ext; unfold raw25391step3 raw25391step2; decide +kernel
      have hl : raw25391step2Labels = labelEmbedding1 ∘ raw25391step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25391step2 raw25391step2Labels raw25391step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw25392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw25392step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25392step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25392step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25392 raw25392Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw25392 raw25392Labels = mixedMoment B raw25392step0 raw25392step0Labels := by
      have ha : raw25392step0 = (fun i j => raw25392 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25392step0 raw25392; decide +kernel
      have hl : raw25392step0Labels = raw25392Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25392 raw25392Labels permutation184 permutation7
    mixedMoment B raw25392step0 raw25392step0Labels = mixedMoment B raw25392step1 raw25392step1Labels := by
      have ha : raw25392step1 = -raw25392step0 := by apply Matrix.ext; change ∀ i j, raw25392step1 i j = -(raw25392step0 i j); unfold raw25392step1 raw25392step0; decide +kernel
      have hl : raw25392step1Labels = raw25392step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25392step1 raw25392step1Labels = mixedMoment B raw25392step2 raw25392step2Labels := by
      have ha : raw25392step2 = raw25392step1 := by apply Matrix.ext; unfold raw25392step2 raw25392step1; decide +kernel
      have hl : raw25392step1Labels = labelEmbedding1 ∘ raw25392step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25392step1 raw25392step1Labels raw25392step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

def raw25393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25393Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25393step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25393step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25393step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw25393step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25393step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25393step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25393step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25393step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25393 raw25393Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw25393 raw25393Labels = mixedMoment B raw25393step0 raw25393step0Labels := by
      have hz : ∀ j, raw25393 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25393step0 = (fun i j => raw25393 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25393step0 raw25393; decide +kernel
      have hl : raw25393step0Labels = raw25393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25393 raw25393Labels permutation520 hz
    mixedMoment B raw25393step0 raw25393step0Labels = mixedMoment B raw25393step1 raw25393step1Labels := by
      have hz : ∀ j, raw25393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25393step1 = (fun i j => raw25393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25393step1 raw25393step0; decide +kernel
      have hl : raw25393step1Labels = raw25393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25393step0 raw25393step0Labels permutation80 hz
    mixedMoment B raw25393step1 raw25393step1Labels = mixedMoment B raw25393step2 raw25393step2Labels := by
      have ha : raw25393step2 = (fun i j => raw25393step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25393step2 raw25393step1; decide +kernel
      have hl : raw25393step2Labels = raw25393step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25393step1 raw25393step1Labels permutation10 permutation7
    mixedMoment B raw25393step2 raw25393step2Labels = mixedMoment B raw25393step3 raw25393step3Labels := by
      have ha : raw25393step3 = -raw25393step2 := by apply Matrix.ext; change ∀ i j, raw25393step3 i j = -(raw25393step2 i j); unfold raw25393step3 raw25393step2; decide +kernel
      have hl : raw25393step3Labels = raw25393step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25393step3 raw25393step3Labels = mixedMoment B raw25393step4 raw25393step4Labels := by
      have ha : raw25393step4 = raw25393step3 := by apply Matrix.ext; unfold raw25393step4 raw25393step3; decide +kernel
      have hl : raw25393step3Labels = labelEmbedding1 ∘ raw25393step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25393step3 raw25393step3Labels raw25393step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw25394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25394Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25394step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw25394step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25394step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25394step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25394step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25394 raw25394Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw25394 raw25394Labels = mixedMoment B raw25394step0 raw25394step0Labels := by
      have hz : ∀ j, raw25394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25394step0 = (fun i j => raw25394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25394step0 raw25394; decide +kernel
      have hl : raw25394step0Labels = raw25394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25394 raw25394Labels permutation346 hz
    mixedMoment B raw25394step0 raw25394step0Labels = mixedMoment B raw25394step1 raw25394step1Labels := by
      have ha : raw25394step1 = (fun i j => raw25394step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25394step1 raw25394step0; decide +kernel
      have hl : raw25394step1Labels = raw25394step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25394step0 raw25394step0Labels permutation40 permutation7
    mixedMoment B raw25394step1 raw25394step1Labels = mixedMoment B raw25394step2 raw25394step2Labels := by
      have ha : raw25394step2 = -raw25394step1 := by apply Matrix.ext; change ∀ i j, raw25394step2 i j = -(raw25394step1 i j); unfold raw25394step2 raw25394step1; decide +kernel
      have hl : raw25394step2Labels = raw25394step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25394step2 raw25394step2Labels = mixedMoment B raw25394step3 raw25394step3Labels := by
      have ha : raw25394step3 = raw25394step2 := by apply Matrix.ext; unfold raw25394step3 raw25394step2; decide +kernel
      have hl : raw25394step2Labels = labelEmbedding1 ∘ raw25394step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25394step2 raw25394step2Labels raw25394step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw25395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25395Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25395step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25395step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25395step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25395step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25395step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25395 raw25395Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw25395 raw25395Labels = mixedMoment B raw25395step0 raw25395step0Labels := by
      have hz : ∀ j, raw25395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25395step0 = (fun i j => raw25395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25395step0 raw25395; decide +kernel
      have hl : raw25395step0Labels = raw25395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25395 raw25395Labels permutation346 hz
    mixedMoment B raw25395step0 raw25395step0Labels = mixedMoment B raw25395step1 raw25395step1Labels := by
      have ha : raw25395step1 = (fun i j => raw25395step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25395step1 raw25395step0; decide +kernel
      have hl : raw25395step1Labels = raw25395step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25395step0 raw25395step0Labels permutation40 permutation7
    mixedMoment B raw25395step1 raw25395step1Labels = mixedMoment B raw25395step2 raw25395step2Labels := by
      have ha : raw25395step2 = -raw25395step1 := by apply Matrix.ext; change ∀ i j, raw25395step2 i j = -(raw25395step1 i j); unfold raw25395step2 raw25395step1; decide +kernel
      have hl : raw25395step2Labels = raw25395step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25395step2 raw25395step2Labels = mixedMoment B raw25395step3 raw25395step3Labels := by
      have ha : raw25395step3 = raw25395step2 := by apply Matrix.ext; unfold raw25395step3 raw25395step2; decide +kernel
      have hl : raw25395step2Labels = labelEmbedding1 ∘ raw25395step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25395step2 raw25395step2Labels raw25395step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1507 node1507Labels := by rfl

def raw25396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25396Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25396step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25396step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25396 raw25396Labels = mixedMoment B node1664 node1664Labels := by
  calc
    mixedMoment B raw25396 raw25396Labels = mixedMoment B raw25396step0 raw25396step0Labels := by
      have ha : raw25396step0 = (fun i j => raw25396 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25396step0 raw25396; decide +kernel
      have hl : raw25396step0Labels = raw25396Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25396 raw25396Labels permutation184 permutation7
    mixedMoment B raw25396step0 raw25396step0Labels = mixedMoment B raw25396step1 raw25396step1Labels := by
      have ha : raw25396step1 = -raw25396step0 := by apply Matrix.ext; change ∀ i j, raw25396step1 i j = -(raw25396step0 i j); unfold raw25396step1 raw25396step0; decide +kernel
      have hl : raw25396step1Labels = raw25396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25396step1 raw25396step1Labels = mixedMoment B raw25396step2 raw25396step2Labels := by
      have ha : raw25396step2 = raw25396step1 := by apply Matrix.ext; unfold raw25396step2 raw25396step1; decide +kernel
      have hl : raw25396step1Labels = labelEmbedding1 ∘ raw25396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25396step1 raw25396step1Labels raw25396step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1664 node1664Labels := by rfl

def raw25397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25397Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25397step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25397step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25397step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25397step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25397step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25397step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25397step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25397 raw25397Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw25397 raw25397Labels = mixedMoment B raw25397step0 raw25397step0Labels := by
      have hz : ∀ j, raw25397 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25397step0 = (fun i j => raw25397 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25397step0 raw25397; decide +kernel
      have hl : raw25397step0Labels = raw25397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25397 raw25397Labels permutation520 hz
    mixedMoment B raw25397step0 raw25397step0Labels = mixedMoment B raw25397step1 raw25397step1Labels := by
      have hz : ∀ j, raw25397step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25397step1 = (fun i j => raw25397step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25397step1 raw25397step0; decide +kernel
      have hl : raw25397step1Labels = raw25397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25397step0 raw25397step0Labels permutation80 hz
    mixedMoment B raw25397step1 raw25397step1Labels = mixedMoment B raw25397step2 raw25397step2Labels := by
      have ha : raw25397step2 = (fun i j => raw25397step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25397step2 raw25397step1; decide +kernel
      have hl : raw25397step2Labels = raw25397step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25397step1 raw25397step1Labels permutation10 permutation7
    mixedMoment B raw25397step2 raw25397step2Labels = mixedMoment B raw25397step3 raw25397step3Labels := by
      have ha : raw25397step3 = -raw25397step2 := by apply Matrix.ext; change ∀ i j, raw25397step3 i j = -(raw25397step2 i j); unfold raw25397step3 raw25397step2; decide +kernel
      have hl : raw25397step3Labels = raw25397step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25397step3 raw25397step3Labels = mixedMoment B raw25397step4 raw25397step4Labels := by
      have ha : raw25397step4 = raw25397step3 := by apply Matrix.ext; unfold raw25397step4 raw25397step3; decide +kernel
      have hl : raw25397step3Labels = labelEmbedding1 ∘ raw25397step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25397step3 raw25397step3Labels raw25397step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw25398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25398Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25398step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25398step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25398step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25398step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25398step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25398step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25398 raw25398Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw25398 raw25398Labels = mixedMoment B raw25398step0 raw25398step0Labels := by
      have hz : ∀ j, raw25398 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25398step0 = (fun i j => raw25398 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25398step0 raw25398; decide +kernel
      have hl : raw25398step0Labels = raw25398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25398 raw25398Labels permutation346 hz
    mixedMoment B raw25398step0 raw25398step0Labels = mixedMoment B raw25398step1 raw25398step1Labels := by
      have ha : raw25398step1 = (fun i j => raw25398step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25398step1 raw25398step0; decide +kernel
      have hl : raw25398step1Labels = raw25398step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25398step0 raw25398step0Labels permutation40 permutation7
    mixedMoment B raw25398step1 raw25398step1Labels = mixedMoment B raw25398step2 raw25398step2Labels := by
      have ha : raw25398step2 = -raw25398step1 := by apply Matrix.ext; change ∀ i j, raw25398step2 i j = -(raw25398step1 i j); unfold raw25398step2 raw25398step1; decide +kernel
      have hl : raw25398step2Labels = raw25398step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25398step2 raw25398step2Labels = mixedMoment B raw25398step3 raw25398step3Labels := by
      have ha : raw25398step3 = raw25398step2 := by apply Matrix.ext; unfold raw25398step3 raw25398step2; decide +kernel
      have hl : raw25398step2Labels = labelEmbedding1 ∘ raw25398step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25398step2 raw25398step2Labels raw25398step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw25399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25399Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw25399step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25399step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25399 raw25399Labels = mixedMoment B node1501 node1501Labels := by
  calc
    mixedMoment B raw25399 raw25399Labels = mixedMoment B raw25399step0 raw25399step0Labels := by
      have ha : raw25399step0 = (fun i j => raw25399 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25399step0 raw25399; decide +kernel
      have hl : raw25399step0Labels = raw25399Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25399 raw25399Labels permutation184 permutation7
    mixedMoment B raw25399step0 raw25399step0Labels = mixedMoment B raw25399step1 raw25399step1Labels := by
      have ha : raw25399step1 = -raw25399step0 := by apply Matrix.ext; change ∀ i j, raw25399step1 i j = -(raw25399step0 i j); unfold raw25399step1 raw25399step0; decide +kernel
      have hl : raw25399step1Labels = raw25399step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25399step1 raw25399step1Labels = mixedMoment B raw25399step2 raw25399step2Labels := by
      have ha : raw25399step2 = raw25399step1 := by apply Matrix.ext; unfold raw25399step2 raw25399step1; decide +kernel
      have hl : raw25399step1Labels = labelEmbedding1 ∘ raw25399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25399step1 raw25399step1Labels raw25399step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1501 node1501Labels := by rfl

def raw25400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25400Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw25400step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25400step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25400step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25400 raw25400Labels = mixedMoment B node1697 node1697Labels := by
  calc
    mixedMoment B raw25400 raw25400Labels = mixedMoment B raw25400step0 raw25400step0Labels := by
      have ha : raw25400step0 = (fun i j => raw25400 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25400step0 raw25400; decide +kernel
      have hl : raw25400step0Labels = raw25400Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25400 raw25400Labels permutation184 permutation7
    mixedMoment B raw25400step0 raw25400step0Labels = mixedMoment B raw25400step1 raw25400step1Labels := by
      have ha : raw25400step1 = -raw25400step0 := by apply Matrix.ext; change ∀ i j, raw25400step1 i j = -(raw25400step0 i j); unfold raw25400step1 raw25400step0; decide +kernel
      have hl : raw25400step1Labels = raw25400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25400step1 raw25400step1Labels = mixedMoment B raw25400step2 raw25400step2Labels := by
      have ha : raw25400step2 = raw25400step1 := by apply Matrix.ext; unfold raw25400step2 raw25400step1; decide +kernel
      have hl : raw25400step1Labels = labelEmbedding1 ∘ raw25400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25400step1 raw25400step1Labels raw25400step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1697 node1697Labels := by rfl

def raw25401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25401Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25401step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw25401step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25401step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25401step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25401 raw25401Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw25401 raw25401Labels = mixedMoment B raw25401step0 raw25401step0Labels := by
      have hz : ∀ j, raw25401 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25401step0 = (fun i j => raw25401 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25401step0 raw25401; decide +kernel
      have hl : raw25401step0Labels = raw25401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25401 raw25401Labels permutation520 hz
    mixedMoment B raw25401step0 raw25401step0Labels = mixedMoment B raw25401step1 raw25401step1Labels := by
      have ha : raw25401step1 = (fun i j => raw25401step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25401step1 raw25401step0; decide +kernel
      have hl : raw25401step1Labels = raw25401step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25401step0 raw25401step0Labels permutation40 permutation7
    mixedMoment B raw25401step1 raw25401step1Labels = mixedMoment B raw25401step2 raw25401step2Labels := by
      have ha : raw25401step2 = -raw25401step1 := by apply Matrix.ext; change ∀ i j, raw25401step2 i j = -(raw25401step1 i j); unfold raw25401step2 raw25401step1; decide +kernel
      have hl : raw25401step2Labels = raw25401step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25401step2 raw25401step2Labels = mixedMoment B raw25401step3 raw25401step3Labels := by
      have ha : raw25401step3 = raw25401step2 := by apply Matrix.ext; unfold raw25401step3 raw25401step2; decide +kernel
      have hl : raw25401step2Labels = labelEmbedding1 ∘ raw25401step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25401step2 raw25401step2Labels raw25401step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw25402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw25402step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25402step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25402step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25402step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25402 raw25402Labels = mixedMoment B node1698 node1698Labels := by
  calc
    mixedMoment B raw25402 raw25402Labels = mixedMoment B raw25402step0 raw25402step0Labels := by
      have ha : raw25402step0 = (fun i j => raw25402 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25402step0 raw25402; decide +kernel
      have hl : raw25402step0Labels = raw25402Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25402 raw25402Labels permutation184 permutation7
    mixedMoment B raw25402step0 raw25402step0Labels = mixedMoment B raw25402step1 raw25402step1Labels := by
      have ha : raw25402step1 = -raw25402step0 := by apply Matrix.ext; change ∀ i j, raw25402step1 i j = -(raw25402step0 i j); unfold raw25402step1 raw25402step0; decide +kernel
      have hl : raw25402step1Labels = raw25402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25402step1 raw25402step1Labels = mixedMoment B raw25402step2 raw25402step2Labels := by
      have ha : raw25402step2 = raw25402step1 := by apply Matrix.ext; unfold raw25402step2 raw25402step1; decide +kernel
      have hl : raw25402step1Labels = labelEmbedding1 ∘ raw25402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25402step1 raw25402step1Labels raw25402step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1698 node1698Labels := by rfl

def raw25403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25403step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25403step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25403step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25403step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25403step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25403step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25403 raw25403Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw25403 raw25403Labels = mixedMoment B raw25403step0 raw25403step0Labels := by
      have hz : ∀ j, raw25403 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25403step0 = (fun i j => raw25403 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25403step0 raw25403; decide +kernel
      have hl : raw25403step0Labels = raw25403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25403 raw25403Labels permutation346 hz
    mixedMoment B raw25403step0 raw25403step0Labels = mixedMoment B raw25403step1 raw25403step1Labels := by
      have ha : raw25403step1 = (fun i j => raw25403step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25403step1 raw25403step0; decide +kernel
      have hl : raw25403step1Labels = raw25403step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25403step0 raw25403step0Labels permutation46 permutation7
    mixedMoment B raw25403step1 raw25403step1Labels = mixedMoment B raw25403step2 raw25403step2Labels := by
      have ha : raw25403step2 = -raw25403step1 := by apply Matrix.ext; change ∀ i j, raw25403step2 i j = -(raw25403step1 i j); unfold raw25403step2 raw25403step1; decide +kernel
      have hl : raw25403step2Labels = raw25403step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25403step2 raw25403step2Labels = mixedMoment B raw25403step3 raw25403step3Labels := by
      have ha : raw25403step3 = raw25403step2 := by apply Matrix.ext; unfold raw25403step3 raw25403step2; decide +kernel
      have hl : raw25403step2Labels = labelEmbedding1 ∘ raw25403step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25403step2 raw25403step2Labels raw25403step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

def raw25404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw25404step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25404step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25404step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25404step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25404 raw25404Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw25404 raw25404Labels = mixedMoment B raw25404step0 raw25404step0Labels := by
      have hz : ∀ j, raw25404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25404step0 = (fun i j => raw25404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25404step0 raw25404; decide +kernel
      have hl : raw25404step0Labels = raw25404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25404 raw25404Labels permutation346 hz
    mixedMoment B raw25404step0 raw25404step0Labels = mixedMoment B raw25404step1 raw25404step1Labels := by
      have ha : raw25404step1 = (fun i j => raw25404step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25404step1 raw25404step0; decide +kernel
      have hl : raw25404step1Labels = raw25404step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25404step0 raw25404step0Labels permutation46 permutation7
    mixedMoment B raw25404step1 raw25404step1Labels = mixedMoment B raw25404step2 raw25404step2Labels := by
      have ha : raw25404step2 = -raw25404step1 := by apply Matrix.ext; change ∀ i j, raw25404step2 i j = -(raw25404step1 i j); unfold raw25404step2 raw25404step1; decide +kernel
      have hl : raw25404step2Labels = raw25404step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25404step2 raw25404step2Labels = mixedMoment B raw25404step3 raw25404step3Labels := by
      have ha : raw25404step3 = raw25404step2 := by apply Matrix.ext; unfold raw25404step3 raw25404step2; decide +kernel
      have hl : raw25404step2Labels = labelEmbedding1 ∘ raw25404step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25404step2 raw25404step2Labels raw25404step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

def raw25405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25405step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25405step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25405step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25405 raw25405Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw25405 raw25405Labels = mixedMoment B raw25405step0 raw25405step0Labels := by
      have ha : raw25405step0 = (fun i j => raw25405 (permutation190 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25405step0 raw25405; decide +kernel
      have hl : raw25405step0Labels = raw25405Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25405 raw25405Labels permutation190 permutation7
    mixedMoment B raw25405step0 raw25405step0Labels = mixedMoment B raw25405step1 raw25405step1Labels := by
      have ha : raw25405step1 = -raw25405step0 := by apply Matrix.ext; change ∀ i j, raw25405step1 i j = -(raw25405step0 i j); unfold raw25405step1 raw25405step0; decide +kernel
      have hl : raw25405step1Labels = raw25405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25405step1 raw25405step1Labels = mixedMoment B raw25405step2 raw25405step2Labels := by
      have ha : raw25405step2 = raw25405step1 := by apply Matrix.ext; unfold raw25405step2 raw25405step1; decide +kernel
      have hl : raw25405step1Labels = labelEmbedding1 ∘ raw25405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25405step1 raw25405step1Labels raw25405step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

def raw25406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25406step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25406step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25406step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25406step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25406step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25406 raw25406Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw25406 raw25406Labels = mixedMoment B raw25406step0 raw25406step0Labels := by
      have hz : ∀ j, raw25406 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25406step0 = (fun i j => raw25406 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25406step0 raw25406; decide +kernel
      have hl : raw25406step0Labels = raw25406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25406 raw25406Labels permutation520 hz
    mixedMoment B raw25406step0 raw25406step0Labels = mixedMoment B raw25406step1 raw25406step1Labels := by
      have hz : ∀ j, raw25406step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25406step1 = (fun i j => raw25406step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25406step1 raw25406step0; decide +kernel
      have hl : raw25406step1Labels = raw25406step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25406step0 raw25406step0Labels permutation80 hz
    mixedMoment B raw25406step1 raw25406step1Labels = mixedMoment B raw25406step2 raw25406step2Labels := by
      have ha : raw25406step2 = (fun i j => raw25406step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25406step2 raw25406step1; decide +kernel
      have hl : raw25406step2Labels = raw25406step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25406step1 raw25406step1Labels permutation10 permutation7
    mixedMoment B raw25406step2 raw25406step2Labels = mixedMoment B raw25406step3 raw25406step3Labels := by
      have ha : raw25406step3 = -raw25406step2 := by apply Matrix.ext; change ∀ i j, raw25406step3 i j = -(raw25406step2 i j); unfold raw25406step3 raw25406step2; decide +kernel
      have hl : raw25406step3Labels = raw25406step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25406step3 raw25406step3Labels = mixedMoment B raw25406step4 raw25406step4Labels := by
      have ha : raw25406step4 = raw25406step3 := by apply Matrix.ext; unfold raw25406step4 raw25406step3; decide +kernel
      have hl : raw25406step3Labels = labelEmbedding1 ∘ raw25406step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25406step3 raw25406step3Labels raw25406step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

def raw25407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25407step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25407step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25407step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25407step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25407step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25407 raw25407Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw25407 raw25407Labels = mixedMoment B raw25407step0 raw25407step0Labels := by
      have hz : ∀ j, raw25407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25407step0 = (fun i j => raw25407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25407step0 raw25407; decide +kernel
      have hl : raw25407step0Labels = raw25407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25407 raw25407Labels permutation346 hz
    mixedMoment B raw25407step0 raw25407step0Labels = mixedMoment B raw25407step1 raw25407step1Labels := by
      have ha : raw25407step1 = (fun i j => raw25407step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25407step1 raw25407step0; decide +kernel
      have hl : raw25407step1Labels = raw25407step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25407step0 raw25407step0Labels permutation46 permutation7
    mixedMoment B raw25407step1 raw25407step1Labels = mixedMoment B raw25407step2 raw25407step2Labels := by
      have ha : raw25407step2 = -raw25407step1 := by apply Matrix.ext; change ∀ i j, raw25407step2 i j = -(raw25407step1 i j); unfold raw25407step2 raw25407step1; decide +kernel
      have hl : raw25407step2Labels = raw25407step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25407step2 raw25407step2Labels = mixedMoment B raw25407step3 raw25407step3Labels := by
      have ha : raw25407step3 = raw25407step2 := by apply Matrix.ext; unfold raw25407step3 raw25407step2; decide +kernel
      have hl : raw25407step2Labels = labelEmbedding1 ∘ raw25407step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25407step2 raw25407step2Labels raw25407step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw25408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25408step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25408step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25408step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25408step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25408 raw25408Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw25408 raw25408Labels = mixedMoment B raw25408step0 raw25408step0Labels := by
      have hz : ∀ j, raw25408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25408step0 = (fun i j => raw25408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25408step0 raw25408; decide +kernel
      have hl : raw25408step0Labels = raw25408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25408 raw25408Labels permutation346 hz
    mixedMoment B raw25408step0 raw25408step0Labels = mixedMoment B raw25408step1 raw25408step1Labels := by
      have ha : raw25408step1 = (fun i j => raw25408step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25408step1 raw25408step0; decide +kernel
      have hl : raw25408step1Labels = raw25408step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25408step0 raw25408step0Labels permutation40 permutation7
    mixedMoment B raw25408step1 raw25408step1Labels = mixedMoment B raw25408step2 raw25408step2Labels := by
      have ha : raw25408step2 = -raw25408step1 := by apply Matrix.ext; change ∀ i j, raw25408step2 i j = -(raw25408step1 i j); unfold raw25408step2 raw25408step1; decide +kernel
      have hl : raw25408step2Labels = raw25408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25408step2 raw25408step2Labels = mixedMoment B raw25408step3 raw25408step3Labels := by
      have ha : raw25408step3 = raw25408step2 := by apply Matrix.ext; unfold raw25408step3 raw25408step2; decide +kernel
      have hl : raw25408step2Labels = labelEmbedding1 ∘ raw25408step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25408step2 raw25408step2Labels raw25408step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

def raw25409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25409step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw25409step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25409step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25409step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw25409step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25409 raw25409Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw25409 raw25409Labels = mixedMoment B raw25409step0 raw25409step0Labels := by
      have hz : ∀ j, raw25409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25409step0 = (fun i j => raw25409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25409step0 raw25409; decide +kernel
      have hl : raw25409step0Labels = raw25409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25409 raw25409Labels permutation346 hz
    mixedMoment B raw25409step0 raw25409step0Labels = mixedMoment B raw25409step1 raw25409step1Labels := by
      have ha : raw25409step1 = (fun i j => raw25409step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25409step1 raw25409step0; decide +kernel
      have hl : raw25409step1Labels = raw25409step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25409step0 raw25409step0Labels permutation40 permutation7
    mixedMoment B raw25409step1 raw25409step1Labels = mixedMoment B raw25409step2 raw25409step2Labels := by
      have ha : raw25409step2 = -raw25409step1 := by apply Matrix.ext; change ∀ i j, raw25409step2 i j = -(raw25409step1 i j); unfold raw25409step2 raw25409step1; decide +kernel
      have hl : raw25409step2Labels = raw25409step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25409step2 raw25409step2Labels = mixedMoment B raw25409step3 raw25409step3Labels := by
      have ha : raw25409step3 = raw25409step2 := by apply Matrix.ext; unfold raw25409step3 raw25409step2; decide +kernel
      have hl : raw25409step2Labels = labelEmbedding1 ∘ raw25409step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25409step2 raw25409step2Labels raw25409step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

def raw25410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw25410step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25410step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25410step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw25410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25410 raw25410Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw25410 raw25410Labels = mixedMoment B raw25410step0 raw25410step0Labels := by
      have ha : raw25410step0 = (fun i j => raw25410 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25410step0 raw25410; decide +kernel
      have hl : raw25410step0Labels = raw25410Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25410 raw25410Labels permutation184 permutation7
    mixedMoment B raw25410step0 raw25410step0Labels = mixedMoment B raw25410step1 raw25410step1Labels := by
      have ha : raw25410step1 = -raw25410step0 := by apply Matrix.ext; change ∀ i j, raw25410step1 i j = -(raw25410step0 i j); unfold raw25410step1 raw25410step0; decide +kernel
      have hl : raw25410step1Labels = raw25410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25410step1 raw25410step1Labels = mixedMoment B raw25410step2 raw25410step2Labels := by
      have ha : raw25410step2 = raw25410step1 := by apply Matrix.ext; unfold raw25410step2 raw25410step1; decide +kernel
      have hl : raw25410step1Labels = labelEmbedding1 ∘ raw25410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25410step1 raw25410step1Labels raw25410step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

def raw25411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw25411step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw25411step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25411step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25411step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw25411step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25411 raw25411Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw25411 raw25411Labels = mixedMoment B raw25411step0 raw25411step0Labels := by
      have hz : ∀ j, raw25411 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25411step0 = (fun i j => raw25411 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25411step0 raw25411; decide +kernel
      have hl : raw25411step0Labels = raw25411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25411 raw25411Labels permutation346 hz
    mixedMoment B raw25411step0 raw25411step0Labels = mixedMoment B raw25411step1 raw25411step1Labels := by
      have ha : raw25411step1 = (fun i j => raw25411step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25411step1 raw25411step0; decide +kernel
      have hl : raw25411step1Labels = raw25411step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25411step0 raw25411step0Labels permutation40 permutation7
    mixedMoment B raw25411step1 raw25411step1Labels = mixedMoment B raw25411step2 raw25411step2Labels := by
      have ha : raw25411step2 = -raw25411step1 := by apply Matrix.ext; change ∀ i j, raw25411step2 i j = -(raw25411step1 i j); unfold raw25411step2 raw25411step1; decide +kernel
      have hl : raw25411step2Labels = raw25411step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25411step2 raw25411step2Labels = mixedMoment B raw25411step3 raw25411step3Labels := by
      have ha : raw25411step3 = raw25411step2 := by apply Matrix.ext; unfold raw25411step3 raw25411step2; decide +kernel
      have hl : raw25411step2Labels = labelEmbedding1 ∘ raw25411step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25411step2 raw25411step2Labels raw25411step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw25412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw25412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw25412step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw25412step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25412step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw25412step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25412step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25412step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25412step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw25412step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25412 raw25412Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw25412 raw25412Labels = mixedMoment B raw25412step0 raw25412step0Labels := by
      have hz : ∀ j, raw25412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw25412step0 = (fun i j => raw25412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw25412step0 raw25412; decide +kernel
      have hl : raw25412step0Labels = raw25412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25412 raw25412Labels permutation434 hz
    mixedMoment B raw25412step0 raw25412step0Labels = mixedMoment B raw25412step1 raw25412step1Labels := by
      have hz : ∀ j, raw25412step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25412step1 = (fun i j => raw25412step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25412step1 raw25412step0; decide +kernel
      have hl : raw25412step1Labels = raw25412step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25412step0 raw25412step0Labels permutation80 hz
    mixedMoment B raw25412step1 raw25412step1Labels = mixedMoment B raw25412step2 raw25412step2Labels := by
      have ha : raw25412step2 = (fun i j => raw25412step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25412step2 raw25412step1; decide +kernel
      have hl : raw25412step2Labels = raw25412step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25412step1 raw25412step1Labels permutation10 permutation7
    mixedMoment B raw25412step2 raw25412step2Labels = mixedMoment B raw25412step3 raw25412step3Labels := by
      have ha : raw25412step3 = -raw25412step2 := by apply Matrix.ext; change ∀ i j, raw25412step3 i j = -(raw25412step2 i j); unfold raw25412step3 raw25412step2; decide +kernel
      have hl : raw25412step3Labels = raw25412step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25412step3 raw25412step3Labels = mixedMoment B raw25412step4 raw25412step4Labels := by
      have ha : raw25412step4 = raw25412step3 := by apply Matrix.ext; unfold raw25412step4 raw25412step3; decide +kernel
      have hl : raw25412step3Labels = labelEmbedding1 ∘ raw25412step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25412step3 raw25412step3Labels raw25412step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw25413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25413 raw25413Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw25413 raw25413Labels = mixedMoment B raw25413step0 raw25413step0Labels := by
      have hz : ∀ j, raw25413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25413step0 = (fun i j => raw25413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25413step0 raw25413; decide +kernel
      have hl : raw25413step0Labels = raw25413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25413 raw25413Labels permutation346 hz
    _ = mixedMoment B node1040 node1040Labels := by rfl

def raw25414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25414 raw25414Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw25414 raw25414Labels = mixedMoment B raw25414step0 raw25414step0Labels := by
      have hz : ∀ j, raw25414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25414step0 = (fun i j => raw25414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25414step0 raw25414; decide +kernel
      have hl : raw25414step0Labels = raw25414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25414 raw25414Labels permutation346 hz
    mixedMoment B raw25414step0 raw25414step0Labels = mixedMoment B raw25414step1 raw25414step1Labels := by
      have ha : raw25414step1 = (fun i j => raw25414step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25414step1 raw25414step0; decide +kernel
      have hl : raw25414step1Labels = raw25414step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25414step0 raw25414step0Labels permutation40 permutation2
    _ = mixedMoment B node600 node600Labels := by rfl

def raw25415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25415 raw25415Labels = mixedMoment B node577 node577Labels := by
  calc
    _ = mixedMoment B node577 node577Labels := by rfl

def raw25416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25416 raw25416Labels = mixedMoment B node582 node582Labels := by
  calc
    mixedMoment B raw25416 raw25416Labels = mixedMoment B raw25416step0 raw25416step0Labels := by
      have hz : ∀ j, raw25416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25416step0 = (fun i j => raw25416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25416step0 raw25416; decide +kernel
      have hl : raw25416step0Labels = raw25416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25416 raw25416Labels permutation346 hz
    mixedMoment B raw25416step0 raw25416step0Labels = mixedMoment B raw25416step1 raw25416step1Labels := by
      have ha : raw25416step1 = (fun i j => raw25416step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25416step1 raw25416step0; decide +kernel
      have hl : raw25416step1Labels = raw25416step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25416step0 raw25416step0Labels permutation34 permutation2
    _ = mixedMoment B node582 node582Labels := by rfl

def raw25417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25417 raw25417Labels = mixedMoment B node582 node582Labels := by
  calc
    mixedMoment B raw25417 raw25417Labels = mixedMoment B raw25417step0 raw25417step0Labels := by
      have hz : ∀ j, raw25417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25417step0 = (fun i j => raw25417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25417step0 raw25417; decide +kernel
      have hl : raw25417step0Labels = raw25417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25417 raw25417Labels permutation346 hz
    _ = mixedMoment B node582 node582Labels := by rfl

def raw25418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25418 raw25418Labels = mixedMoment B node919 node919Labels := by
  calc
    mixedMoment B raw25418 raw25418Labels = mixedMoment B raw25418step0 raw25418step0Labels := by
      have ha : raw25418step0 = (fun i j => raw25418 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25418step0 raw25418; decide +kernel
      have hl : raw25418step0Labels = raw25418Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25418 raw25418Labels permutation184 permutation2
    _ = mixedMoment B node919 node919Labels := by rfl

def raw25419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25419 raw25419Labels = mixedMoment B node1082 node1082Labels := by
  calc
    mixedMoment B raw25419 raw25419Labels = mixedMoment B raw25419step0 raw25419step0Labels := by
      have hz : ∀ j, raw25419 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25419step0 = (fun i j => raw25419 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25419step0 raw25419; decide +kernel
      have hl : raw25419step0Labels = raw25419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25419 raw25419Labels permutation520 hz
    mixedMoment B raw25419step0 raw25419step0Labels = mixedMoment B raw25419step1 raw25419step1Labels := by
      have hz : ∀ j, raw25419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25419step1 = (fun i j => raw25419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25419step1 raw25419step0; decide +kernel
      have hl : raw25419step1Labels = raw25419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25419step0 raw25419step0Labels permutation80 hz
    mixedMoment B raw25419step1 raw25419step1Labels = mixedMoment B raw25419step2 raw25419step2Labels := by
      have ha : raw25419step2 = (fun i j => raw25419step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25419step2 raw25419step1; decide +kernel
      have hl : raw25419step2Labels = raw25419step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25419step1 raw25419step1Labels permutation10 permutation2
    _ = mixedMoment B node1082 node1082Labels := by rfl

def raw25420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25420 raw25420Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw25420 raw25420Labels = mixedMoment B raw25420step0 raw25420step0Labels := by
      have hz : ∀ j, raw25420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25420step0 = (fun i j => raw25420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25420step0 raw25420; decide +kernel
      have hl : raw25420step0Labels = raw25420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25420 raw25420Labels permutation346 hz
    mixedMoment B raw25420step0 raw25420step0Labels = mixedMoment B raw25420step1 raw25420step1Labels := by
      have ha : raw25420step1 = (fun i j => raw25420step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25420step1 raw25420step0; decide +kernel
      have hl : raw25420step1Labels = raw25420step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25420step0 raw25420step0Labels permutation40 permutation2
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw25421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25421 raw25421Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw25421 raw25421Labels = mixedMoment B raw25421step0 raw25421step0Labels := by
      have hz : ∀ j, raw25421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25421step0 = (fun i j => raw25421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25421step0 raw25421; decide +kernel
      have hl : raw25421step0Labels = raw25421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25421 raw25421Labels permutation346 hz
    _ = mixedMoment B node2106 node2106Labels := by rfl

def raw25422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25422 raw25422Labels = mixedMoment B node941 node941Labels := by
  calc
    _ = mixedMoment B node941 node941Labels := by rfl

def raw25423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25423 raw25423Labels = mixedMoment B node946 node946Labels := by
  calc
    mixedMoment B raw25423 raw25423Labels = mixedMoment B raw25423step0 raw25423step0Labels := by
      have hz : ∀ j, raw25423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25423step0 = (fun i j => raw25423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25423step0 raw25423; decide +kernel
      have hl : raw25423step0Labels = raw25423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25423 raw25423Labels permutation346 hz
    mixedMoment B raw25423step0 raw25423step0Labels = mixedMoment B raw25423step1 raw25423step1Labels := by
      have ha : raw25423step1 = (fun i j => raw25423step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25423step1 raw25423step0; decide +kernel
      have hl : raw25423step1Labels = raw25423step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25423step0 raw25423step0Labels permutation34 permutation2
    _ = mixedMoment B node946 node946Labels := by rfl

def raw25424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25424 raw25424Labels = mixedMoment B node946 node946Labels := by
  calc
    mixedMoment B raw25424 raw25424Labels = mixedMoment B raw25424step0 raw25424step0Labels := by
      have hz : ∀ j, raw25424 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25424step0 = (fun i j => raw25424 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25424step0 raw25424; decide +kernel
      have hl : raw25424step0Labels = raw25424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25424 raw25424Labels permutation346 hz
    _ = mixedMoment B node946 node946Labels := by rfl

def raw25425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25425 raw25425Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw25425 raw25425Labels = mixedMoment B raw25425step0 raw25425step0Labels := by
      have hz : ∀ j, raw25425 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25425step0 = (fun i j => raw25425 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25425step0 raw25425; decide +kernel
      have hl : raw25425step0Labels = raw25425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25425 raw25425Labels permutation520 hz
    _ = mixedMoment B node1040 node1040Labels := by rfl

def raw25426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25426 raw25426Labels = mixedMoment B node1038 node1038Labels := by
  calc
    _ = mixedMoment B node1038 node1038Labels := by rfl

def raw25427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25427step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25427step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25427 raw25427Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw25427 raw25427Labels = mixedMoment B raw25427step0 raw25427step0Labels := by
      have hz : ∀ j, raw25427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25427step0 = (fun i j => raw25427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25427step0 raw25427; decide +kernel
      have hl : raw25427step0Labels = raw25427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25427 raw25427Labels permutation346 hz
    mixedMoment B raw25427step0 raw25427step0Labels = mixedMoment B raw25427step1 raw25427step1Labels := by
      have ha : raw25427step1 = (fun i j => raw25427step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25427step1 raw25427step0; decide +kernel
      have hl : raw25427step1Labels = raw25427step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25427step0 raw25427step0Labels permutation38 permutation3
    mixedMoment B raw25427step1 raw25427step1Labels = mixedMoment B raw25427step2 raw25427step2Labels := by
      have ha : raw25427step2 = raw25427step1 := by apply Matrix.ext; unfold raw25427step2 raw25427step1; decide +kernel
      have hl : raw25427step1Labels = labelEmbedding6 ∘ raw25427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25427step1 raw25427step1Labels raw25427step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw25428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25428step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25428 raw25428Labels = mixedMoment B node4115 node4115Labels := by
  calc
    mixedMoment B raw25428 raw25428Labels = mixedMoment B raw25428step0 raw25428step0Labels := by
      have hz : ∀ j, raw25428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25428step0 = (fun i j => raw25428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25428step0 raw25428; decide +kernel
      have hl : raw25428step0Labels = raw25428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25428 raw25428Labels permutation346 hz
    mixedMoment B raw25428step0 raw25428step0Labels = mixedMoment B raw25428step1 raw25428step1Labels := by
      have ha : raw25428step1 = (fun i j => raw25428step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25428step1 raw25428step0; decide +kernel
      have hl : raw25428step1Labels = raw25428step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25428step0 raw25428step0Labels permutation40 permutation3
    mixedMoment B raw25428step1 raw25428step1Labels = mixedMoment B raw25428step2 raw25428step2Labels := by
      have ha : raw25428step2 = raw25428step1 := by apply Matrix.ext; unfold raw25428step2 raw25428step1; decide +kernel
      have hl : raw25428step1Labels = labelEmbedding6 ∘ raw25428step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25428step1 raw25428step1Labels raw25428step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4115 node4115Labels := by rfl

def raw25429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25429step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25429 raw25429Labels = mixedMoment B node4298 node4298Labels := by
  calc
    mixedMoment B raw25429 raw25429Labels = mixedMoment B raw25429step0 raw25429step0Labels := by
      have ha : raw25429step0 = (fun i j => raw25429 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25429step0 raw25429; decide +kernel
      have hl : raw25429step0Labels = raw25429Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25429 raw25429Labels permutation184 permutation3
    mixedMoment B raw25429step0 raw25429step0Labels = mixedMoment B raw25429step1 raw25429step1Labels := by
      have ha : raw25429step1 = raw25429step0 := by apply Matrix.ext; unfold raw25429step1 raw25429step0; decide +kernel
      have hl : raw25429step0Labels = labelEmbedding6 ∘ raw25429step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25429step0 raw25429step0Labels raw25429step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4298 node4298Labels := by rfl

def raw25430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25430step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25430 raw25430Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw25430 raw25430Labels = mixedMoment B raw25430step0 raw25430step0Labels := by
      have hz : ∀ j, raw25430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25430step0 = (fun i j => raw25430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25430step0 raw25430; decide +kernel
      have hl : raw25430step0Labels = raw25430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25430 raw25430Labels permutation346 hz
    mixedMoment B raw25430step0 raw25430step0Labels = mixedMoment B raw25430step1 raw25430step1Labels := by
      have ha : raw25430step1 = (fun i j => raw25430step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25430step1 raw25430step0; decide +kernel
      have hl : raw25430step1Labels = raw25430step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25430step0 raw25430step0Labels permutation46 permutation3
    mixedMoment B raw25430step1 raw25430step1Labels = mixedMoment B raw25430step2 raw25430step2Labels := by
      have ha : raw25430step2 = raw25430step1 := by apply Matrix.ext; unfold raw25430step2 raw25430step1; decide +kernel
      have hl : raw25430step1Labels = labelEmbedding6 ∘ raw25430step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25430step1 raw25430step1Labels raw25430step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw25431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25431step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25431step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25431 raw25431Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25431 raw25431Labels = mixedMoment B raw25431step0 raw25431step0Labels := by
      have hz : ∀ j, raw25431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25431step0 = (fun i j => raw25431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25431step0 raw25431; decide +kernel
      have hl : raw25431step0Labels = raw25431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25431 raw25431Labels permutation346 hz
    mixedMoment B raw25431step0 raw25431step0Labels = mixedMoment B raw25431step1 raw25431step1Labels := by
      have ha : raw25431step1 = (fun i j => raw25431step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25431step1 raw25431step0; decide +kernel
      have hl : raw25431step1Labels = raw25431step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25431step0 raw25431step0Labels permutation41 permutation3
    mixedMoment B raw25431step1 raw25431step1Labels = mixedMoment B raw25431step2 raw25431step2Labels := by
      have ha : raw25431step2 = raw25431step1 := by apply Matrix.ext; unfold raw25431step2 raw25431step1; decide +kernel
      have hl : raw25431step1Labels = labelEmbedding6 ∘ raw25431step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25431step1 raw25431step1Labels raw25431step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw25432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25432step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25432 raw25432Labels = mixedMoment B node4098 node4098Labels := by
  calc
    mixedMoment B raw25432 raw25432Labels = mixedMoment B raw25432step0 raw25432step0Labels := by
      have ha : raw25432step0 = (fun i j => raw25432 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25432step0 raw25432; decide +kernel
      have hl : raw25432step0Labels = raw25432Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25432 raw25432Labels permutation160 permutation3
    mixedMoment B raw25432step0 raw25432step0Labels = mixedMoment B raw25432step1 raw25432step1Labels := by
      have ha : raw25432step1 = raw25432step0 := by apply Matrix.ext; unfold raw25432step1 raw25432step0; decide +kernel
      have hl : raw25432step0Labels = labelEmbedding6 ∘ raw25432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25432step0 raw25432step0Labels raw25432step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4098 node4098Labels := by rfl

def raw25433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25433step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25433 raw25433Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw25433 raw25433Labels = mixedMoment B raw25433step0 raw25433step0Labels := by
      have ha : raw25433step0 = (fun i j => raw25433 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25433step0 raw25433; decide +kernel
      have hl : raw25433step0Labels = raw25433Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25433 raw25433Labels permutation160 permutation3
    mixedMoment B raw25433step0 raw25433step0Labels = mixedMoment B raw25433step1 raw25433step1Labels := by
      have ha : raw25433step1 = raw25433step0 := by apply Matrix.ext; unfold raw25433step1 raw25433step0; decide +kernel
      have hl : raw25433step0Labels = labelEmbedding6 ∘ raw25433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25433step0 raw25433step0Labels raw25433step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

def raw25434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25434step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25434 raw25434Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw25434 raw25434Labels = mixedMoment B raw25434step0 raw25434step0Labels := by
      have ha : raw25434step0 = (fun i j => raw25434 (permutation226 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25434step0 raw25434; decide +kernel
      have hl : raw25434step0Labels = raw25434Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25434 raw25434Labels permutation226 permutation3
    mixedMoment B raw25434step0 raw25434step0Labels = mixedMoment B raw25434step1 raw25434step1Labels := by
      have ha : raw25434step1 = raw25434step0 := by apply Matrix.ext; unfold raw25434step1 raw25434step0; decide +kernel
      have hl : raw25434step0Labels = labelEmbedding6 ∘ raw25434step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25434step0 raw25434step0Labels raw25434step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw25435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25435step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25435step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25435 raw25435Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw25435 raw25435Labels = mixedMoment B raw25435step0 raw25435step0Labels := by
      have ha : raw25435step0 = (fun i j => raw25435 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25435step0 raw25435; decide +kernel
      have hl : raw25435step0Labels = raw25435Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25435 raw25435Labels permutation160 permutation3
    mixedMoment B raw25435step0 raw25435step0Labels = mixedMoment B raw25435step1 raw25435step1Labels := by
      have ha : raw25435step1 = raw25435step0 := by apply Matrix.ext; unfold raw25435step1 raw25435step0; decide +kernel
      have hl : raw25435step0Labels = labelEmbedding6 ∘ raw25435step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25435step0 raw25435step0Labels raw25435step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw25436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25436step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25436step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25436 raw25436Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw25436 raw25436Labels = mixedMoment B raw25436step0 raw25436step0Labels := by
      have hz : ∀ j, raw25436 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25436step0 = (fun i j => raw25436 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25436step0 raw25436; decide +kernel
      have hl : raw25436step0Labels = raw25436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25436 raw25436Labels permutation346 hz
    mixedMoment B raw25436step0 raw25436step0Labels = mixedMoment B raw25436step1 raw25436step1Labels := by
      have ha : raw25436step1 = (fun i j => raw25436step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25436step1 raw25436step0; decide +kernel
      have hl : raw25436step1Labels = raw25436step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25436step0 raw25436step0Labels permutation34 permutation3
    mixedMoment B raw25436step1 raw25436step1Labels = mixedMoment B raw25436step2 raw25436step2Labels := by
      have ha : raw25436step2 = raw25436step1 := by apply Matrix.ext; unfold raw25436step2 raw25436step1; decide +kernel
      have hl : raw25436step1Labels = labelEmbedding6 ∘ raw25436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25436step1 raw25436step1Labels raw25436step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4102 node4102Labels := by rfl

def raw25437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25437step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25437step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25437 raw25437Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25437 raw25437Labels = mixedMoment B raw25437step0 raw25437step0Labels := by
      have hz : ∀ j, raw25437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25437step0 = (fun i j => raw25437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25437step0 raw25437; decide +kernel
      have hl : raw25437step0Labels = raw25437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25437 raw25437Labels permutation346 hz
    mixedMoment B raw25437step0 raw25437step0Labels = mixedMoment B raw25437step1 raw25437step1Labels := by
      have ha : raw25437step1 = (fun i j => raw25437step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25437step1 raw25437step0; decide +kernel
      have hl : raw25437step1Labels = raw25437step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25437step0 raw25437step0Labels permutation34 permutation3
    mixedMoment B raw25437step1 raw25437step1Labels = mixedMoment B raw25437step2 raw25437step2Labels := by
      have ha : raw25437step2 = raw25437step1 := by apply Matrix.ext; unfold raw25437step2 raw25437step1; decide +kernel
      have hl : raw25437step1Labels = labelEmbedding6 ∘ raw25437step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25437step1 raw25437step1Labels raw25437step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw25438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25438step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25438step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25438 raw25438Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw25438 raw25438Labels = mixedMoment B raw25438step0 raw25438step0Labels := by
      have ha : raw25438step0 = (fun i j => raw25438 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25438step0 raw25438; decide +kernel
      have hl : raw25438step0Labels = raw25438Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25438 raw25438Labels permutation178 permutation3
    mixedMoment B raw25438step0 raw25438step0Labels = mixedMoment B raw25438step1 raw25438step1Labels := by
      have ha : raw25438step1 = raw25438step0 := by apply Matrix.ext; unfold raw25438step1 raw25438step0; decide +kernel
      have hl : raw25438step0Labels = labelEmbedding6 ∘ raw25438step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25438step0 raw25438step0Labels raw25438step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4288 node4288Labels := by rfl

def raw25439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25439step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25439step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25439 raw25439Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw25439 raw25439Labels = mixedMoment B raw25439step0 raw25439step0Labels := by
      have hz : ∀ j, raw25439 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25439step0 = (fun i j => raw25439 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25439step0 raw25439; decide +kernel
      have hl : raw25439step0Labels = raw25439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25439 raw25439Labels permutation346 hz
    mixedMoment B raw25439step0 raw25439step0Labels = mixedMoment B raw25439step1 raw25439step1Labels := by
      have ha : raw25439step1 = (fun i j => raw25439step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25439step1 raw25439step0; decide +kernel
      have hl : raw25439step1Labels = raw25439step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25439step0 raw25439step0Labels permutation44 permutation3
    mixedMoment B raw25439step1 raw25439step1Labels = mixedMoment B raw25439step2 raw25439step2Labels := by
      have ha : raw25439step2 = raw25439step1 := by apply Matrix.ext; unfold raw25439step2 raw25439step1; decide +kernel
      have hl : raw25439step1Labels = labelEmbedding6 ∘ raw25439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25439step1 raw25439step1Labels raw25439step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw25440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25440step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25440step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25440 raw25440Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25440 raw25440Labels = mixedMoment B raw25440step0 raw25440step0Labels := by
      have hz : ∀ j, raw25440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25440step0 = (fun i j => raw25440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25440step0 raw25440; decide +kernel
      have hl : raw25440step0Labels = raw25440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25440 raw25440Labels permutation346 hz
    mixedMoment B raw25440step0 raw25440step0Labels = mixedMoment B raw25440step1 raw25440step1Labels := by
      have ha : raw25440step1 = (fun i j => raw25440step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25440step1 raw25440step0; decide +kernel
      have hl : raw25440step1Labels = raw25440step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25440step0 raw25440step0Labels permutation35 permutation3
    mixedMoment B raw25440step1 raw25440step1Labels = mixedMoment B raw25440step2 raw25440step2Labels := by
      have ha : raw25440step2 = raw25440step1 := by apply Matrix.ext; unfold raw25440step2 raw25440step1; decide +kernel
      have hl : raw25440step1Labels = labelEmbedding6 ∘ raw25440step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25440step1 raw25440step1Labels raw25440step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw25441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25441step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25441step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25441 raw25441Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw25441 raw25441Labels = mixedMoment B raw25441step0 raw25441step0Labels := by
      have hz : ∀ j, raw25441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25441step0 = (fun i j => raw25441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25441step0 raw25441; decide +kernel
      have hl : raw25441step0Labels = raw25441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25441 raw25441Labels permutation346 hz
    mixedMoment B raw25441step0 raw25441step0Labels = mixedMoment B raw25441step1 raw25441step1Labels := by
      have ha : raw25441step1 = (fun i j => raw25441step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25441step1 raw25441step0; decide +kernel
      have hl : raw25441step1Labels = raw25441step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25441step0 raw25441step0Labels permutation32 permutation3
    mixedMoment B raw25441step1 raw25441step1Labels = mixedMoment B raw25441step2 raw25441step2Labels := by
      have ha : raw25441step2 = raw25441step1 := by apply Matrix.ext; unfold raw25441step2 raw25441step1; decide +kernel
      have hl : raw25441step1Labels = labelEmbedding6 ∘ raw25441step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25441step1 raw25441step1Labels raw25441step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4102 node4102Labels := by rfl

def raw25442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25442step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25442step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25442 raw25442Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25442 raw25442Labels = mixedMoment B raw25442step0 raw25442step0Labels := by
      have hz : ∀ j, raw25442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25442step0 = (fun i j => raw25442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25442step0 raw25442; decide +kernel
      have hl : raw25442step0Labels = raw25442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25442 raw25442Labels permutation346 hz
    mixedMoment B raw25442step0 raw25442step0Labels = mixedMoment B raw25442step1 raw25442step1Labels := by
      have ha : raw25442step1 = (fun i j => raw25442step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25442step1 raw25442step0; decide +kernel
      have hl : raw25442step1Labels = raw25442step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25442step0 raw25442step0Labels permutation32 permutation3
    mixedMoment B raw25442step1 raw25442step1Labels = mixedMoment B raw25442step2 raw25442step2Labels := by
      have ha : raw25442step2 = raw25442step1 := by apply Matrix.ext; unfold raw25442step2 raw25442step1; decide +kernel
      have hl : raw25442step1Labels = labelEmbedding6 ∘ raw25442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25442step1 raw25442step1Labels raw25442step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw25443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25443step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25443 raw25443Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw25443 raw25443Labels = mixedMoment B raw25443step0 raw25443step0Labels := by
      have ha : raw25443step0 = (fun i j => raw25443 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25443step0 raw25443; decide +kernel
      have hl : raw25443step0Labels = raw25443Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25443 raw25443Labels permutation176 permutation3
    mixedMoment B raw25443step0 raw25443step0Labels = mixedMoment B raw25443step1 raw25443step1Labels := by
      have ha : raw25443step1 = raw25443step0 := by apply Matrix.ext; unfold raw25443step1 raw25443step0; decide +kernel
      have hl : raw25443step0Labels = labelEmbedding6 ∘ raw25443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25443step0 raw25443step0Labels raw25443step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4288 node4288Labels := by rfl

def raw25444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25444step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25444step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25444step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25444 raw25444Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25444 raw25444Labels = mixedMoment B raw25444step0 raw25444step0Labels := by
      have hz : ∀ j, raw25444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25444step0 = (fun i j => raw25444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25444step0 raw25444; decide +kernel
      have hl : raw25444step0Labels = raw25444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25444 raw25444Labels permutation346 hz
    mixedMoment B raw25444step0 raw25444step0Labels = mixedMoment B raw25444step1 raw25444step1Labels := by
      have ha : raw25444step1 = (fun i j => raw25444step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25444step1 raw25444step0; decide +kernel
      have hl : raw25444step1Labels = raw25444step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25444step0 raw25444step0Labels permutation33 permutation3
    mixedMoment B raw25444step1 raw25444step1Labels = mixedMoment B raw25444step2 raw25444step2Labels := by
      have ha : raw25444step2 = raw25444step1 := by apply Matrix.ext; unfold raw25444step2 raw25444step1; decide +kernel
      have hl : raw25444step1Labels = labelEmbedding6 ∘ raw25444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25444step1 raw25444step1Labels raw25444step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw25445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25445step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25445step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25445 raw25445Labels = mixedMoment B node4099 node4099Labels := by
  calc
    mixedMoment B raw25445 raw25445Labels = mixedMoment B raw25445step0 raw25445step0Labels := by
      have hz : ∀ j, raw25445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25445step0 = (fun i j => raw25445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25445step0 raw25445; decide +kernel
      have hl : raw25445step0Labels = raw25445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25445 raw25445Labels permutation346 hz
    mixedMoment B raw25445step0 raw25445step0Labels = mixedMoment B raw25445step1 raw25445step1Labels := by
      have ha : raw25445step1 = (fun i j => raw25445step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25445step1 raw25445step0; decide +kernel
      have hl : raw25445step1Labels = raw25445step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25445step0 raw25445step0Labels permutation32 permutation3
    mixedMoment B raw25445step1 raw25445step1Labels = mixedMoment B raw25445step2 raw25445step2Labels := by
      have ha : raw25445step2 = raw25445step1 := by apply Matrix.ext; unfold raw25445step2 raw25445step1; decide +kernel
      have hl : raw25445step1Labels = labelEmbedding6 ∘ raw25445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25445step1 raw25445step1Labels raw25445step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4099 node4099Labels := by rfl

def raw25446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25446step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25446step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25446 raw25446Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw25446 raw25446Labels = mixedMoment B raw25446step0 raw25446step0Labels := by
      have hz : ∀ j, raw25446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25446step0 = (fun i j => raw25446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25446step0 raw25446; decide +kernel
      have hl : raw25446step0Labels = raw25446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25446 raw25446Labels permutation346 hz
    mixedMoment B raw25446step0 raw25446step0Labels = mixedMoment B raw25446step1 raw25446step1Labels := by
      have ha : raw25446step1 = (fun i j => raw25446step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25446step1 raw25446step0; decide +kernel
      have hl : raw25446step1Labels = raw25446step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25446step0 raw25446step0Labels permutation32 permutation3
    mixedMoment B raw25446step1 raw25446step1Labels = mixedMoment B raw25446step2 raw25446step2Labels := by
      have ha : raw25446step2 = raw25446step1 := by apply Matrix.ext; unfold raw25446step2 raw25446step1; decide +kernel
      have hl : raw25446step1Labels = labelEmbedding6 ∘ raw25446step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25446step1 raw25446step1Labels raw25446step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4343 node4343Labels := by rfl

def raw25447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25447step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25447step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25447 raw25447Labels = mixedMoment B node4286 node4286Labels := by
  calc
    mixedMoment B raw25447 raw25447Labels = mixedMoment B raw25447step0 raw25447step0Labels := by
      have ha : raw25447step0 = (fun i j => raw25447 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25447step0 raw25447; decide +kernel
      have hl : raw25447step0Labels = raw25447Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25447 raw25447Labels permutation176 permutation3
    mixedMoment B raw25447step0 raw25447step0Labels = mixedMoment B raw25447step1 raw25447step1Labels := by
      have ha : raw25447step1 = raw25447step0 := by apply Matrix.ext; unfold raw25447step1 raw25447step0; decide +kernel
      have hl : raw25447step0Labels = labelEmbedding6 ∘ raw25447step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25447step0 raw25447step0Labels raw25447step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4286 node4286Labels := by rfl

def raw25448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25448step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw25448step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw25448step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25448 raw25448Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw25448 raw25448Labels = mixedMoment B raw25448step0 raw25448step0Labels := by
      have hz : ∀ j, raw25448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25448step0 = (fun i j => raw25448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25448step0 raw25448; decide +kernel
      have hl : raw25448step0Labels = raw25448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25448 raw25448Labels permutation346 hz
    mixedMoment B raw25448step0 raw25448step0Labels = mixedMoment B raw25448step1 raw25448step1Labels := by
      have ha : raw25448step1 = (fun i j => raw25448step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25448step1 raw25448step0; decide +kernel
      have hl : raw25448step1Labels = raw25448step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25448step0 raw25448step0Labels permutation44 permutation3
    mixedMoment B raw25448step1 raw25448step1Labels = mixedMoment B raw25448step2 raw25448step2Labels := by
      have ha : raw25448step2 = raw25448step1 := by apply Matrix.ext; unfold raw25448step2 raw25448step1; decide +kernel
      have hl : raw25448step1Labels = labelEmbedding6 ∘ raw25448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25448step1 raw25448step1Labels raw25448step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

def raw25449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25449step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw25449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25449 raw25449Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw25449 raw25449Labels = mixedMoment B raw25449step0 raw25449step0Labels := by
      have hz : ∀ j, raw25449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25449step0 = (fun i j => raw25449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25449step0 raw25449; decide +kernel
      have hl : raw25449step0Labels = raw25449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25449 raw25449Labels permutation346 hz
    mixedMoment B raw25449step0 raw25449step0Labels = mixedMoment B raw25449step1 raw25449step1Labels := by
      have ha : raw25449step1 = (fun i j => raw25449step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25449step1 raw25449step0; decide +kernel
      have hl : raw25449step1Labels = raw25449step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25449step0 raw25449step0Labels permutation38 permutation3
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw25450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25450step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25450 raw25450Labels = mixedMoment B node552 node552Labels := by
  calc
    mixedMoment B raw25450 raw25450Labels = mixedMoment B raw25450step0 raw25450step0Labels := by
      have hz : ∀ j, raw25450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25450step0 = (fun i j => raw25450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25450step0 raw25450; decide +kernel
      have hl : raw25450step0Labels = raw25450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25450 raw25450Labels permutation346 hz
    mixedMoment B raw25450step0 raw25450step0Labels = mixedMoment B raw25450step1 raw25450step1Labels := by
      have ha : raw25450step1 = (fun i j => raw25450step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25450step1 raw25450step0; decide +kernel
      have hl : raw25450step1Labels = raw25450step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25450step0 raw25450step0Labels permutation40 permutation3
    _ = mixedMoment B node552 node552Labels := by rfl

def raw25451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25451Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25451 raw25451Labels = mixedMoment B node876 node876Labels := by
  calc
    mixedMoment B raw25451 raw25451Labels = mixedMoment B raw25451step0 raw25451step0Labels := by
      have ha : raw25451step0 = (fun i j => raw25451 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25451step0 raw25451; decide +kernel
      have hl : raw25451step0Labels = raw25451Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25451 raw25451Labels permutation184 permutation3
    _ = mixedMoment B node876 node876Labels := by rfl

def raw25452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25452Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25452step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw25452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25452 raw25452Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw25452 raw25452Labels = mixedMoment B raw25452step0 raw25452step0Labels := by
      have hz : ∀ j, raw25452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25452step0 = (fun i j => raw25452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25452step0 raw25452; decide +kernel
      have hl : raw25452step0Labels = raw25452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25452 raw25452Labels permutation346 hz
    mixedMoment B raw25452step0 raw25452step0Labels = mixedMoment B raw25452step1 raw25452step1Labels := by
      have ha : raw25452step1 = (fun i j => raw25452step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25452step1 raw25452step0; decide +kernel
      have hl : raw25452step1Labels = raw25452step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25452step0 raw25452step0Labels permutation46 permutation3
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw25453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25453Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25453step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25453 raw25453Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw25453 raw25453Labels = mixedMoment B raw25453step0 raw25453step0Labels := by
      have hz : ∀ j, raw25453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25453step0 = (fun i j => raw25453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25453step0 raw25453; decide +kernel
      have hl : raw25453step0Labels = raw25453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25453 raw25453Labels permutation346 hz
    mixedMoment B raw25453step0 raw25453step0Labels = mixedMoment B raw25453step1 raw25453step1Labels := by
      have ha : raw25453step1 = (fun i j => raw25453step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25453step1 raw25453step0; decide +kernel
      have hl : raw25453step1Labels = raw25453step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25453step0 raw25453step0Labels permutation41 permutation3
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw25454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25454Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25454 raw25454Labels = mixedMoment B node535 node535Labels := by
  calc
    mixedMoment B raw25454 raw25454Labels = mixedMoment B raw25454step0 raw25454step0Labels := by
      have ha : raw25454step0 = (fun i j => raw25454 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25454step0 raw25454; decide +kernel
      have hl : raw25454step0Labels = raw25454Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25454 raw25454Labels permutation160 permutation3
    _ = mixedMoment B node535 node535Labels := by rfl

def raw25455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25455Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25455 raw25455Labels = mixedMoment B node919 node919Labels := by
  calc
    mixedMoment B raw25455 raw25455Labels = mixedMoment B raw25455step0 raw25455step0Labels := by
      have ha : raw25455step0 = (fun i j => raw25455 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25455step0 raw25455; decide +kernel
      have hl : raw25455step0Labels = raw25455Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25455 raw25455Labels permutation160 permutation3
    _ = mixedMoment B node919 node919Labels := by rfl

def raw25456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25456Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25456 raw25456Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw25456 raw25456Labels = mixedMoment B raw25456step0 raw25456step0Labels := by
      have ha : raw25456step0 = (fun i j => raw25456 (permutation226 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25456step0 raw25456; decide +kernel
      have hl : raw25456step0Labels = raw25456Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25456 raw25456Labels permutation226 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

def raw25457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25457 raw25457Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw25457 raw25457Labels = mixedMoment B raw25457step0 raw25457step0Labels := by
      have ha : raw25457step0 = (fun i j => raw25457 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25457step0 raw25457; decide +kernel
      have hl : raw25457step0Labels = raw25457Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25457 raw25457Labels permutation160 permutation3
    _ = mixedMoment B node1039 node1039Labels := by rfl

def raw25458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25458step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25458 raw25458Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw25458 raw25458Labels = mixedMoment B raw25458step0 raw25458step0Labels := by
      have hz : ∀ j, raw25458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25458step0 = (fun i j => raw25458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25458step0 raw25458; decide +kernel
      have hl : raw25458step0Labels = raw25458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25458 raw25458Labels permutation346 hz
    mixedMoment B raw25458step0 raw25458step0Labels = mixedMoment B raw25458step1 raw25458step1Labels := by
      have ha : raw25458step1 = (fun i j => raw25458step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25458step1 raw25458step0; decide +kernel
      have hl : raw25458step1Labels = raw25458step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25458step0 raw25458step0Labels permutation34 permutation3
    _ = mixedMoment B node539 node539Labels := by rfl

def raw25459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25459step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25459 raw25459Labels = mixedMoment B node927 node927Labels := by
  calc
    mixedMoment B raw25459 raw25459Labels = mixedMoment B raw25459step0 raw25459step0Labels := by
      have hz : ∀ j, raw25459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25459step0 = (fun i j => raw25459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25459step0 raw25459; decide +kernel
      have hl : raw25459step0Labels = raw25459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25459 raw25459Labels permutation346 hz
    mixedMoment B raw25459step0 raw25459step0Labels = mixedMoment B raw25459step1 raw25459step1Labels := by
      have ha : raw25459step1 = (fun i j => raw25459step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25459step1 raw25459step0; decide +kernel
      have hl : raw25459step1Labels = raw25459step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25459step0 raw25459step0Labels permutation34 permutation3
    _ = mixedMoment B node927 node927Labels := by rfl

def raw25460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25460 raw25460Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw25460 raw25460Labels = mixedMoment B raw25460step0 raw25460step0Labels := by
      have ha : raw25460step0 = (fun i j => raw25460 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25460step0 raw25460; decide +kernel
      have hl : raw25460step0Labels = raw25460Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25460 raw25460Labels permutation178 permutation3
    _ = mixedMoment B node866 node866Labels := by rfl

def raw25461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25461step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25461 raw25461Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw25461 raw25461Labels = mixedMoment B raw25461step0 raw25461step0Labels := by
      have hz : ∀ j, raw25461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25461step0 = (fun i j => raw25461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25461step0 raw25461; decide +kernel
      have hl : raw25461step0Labels = raw25461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25461 raw25461Labels permutation346 hz
    mixedMoment B raw25461step0 raw25461step0Labels = mixedMoment B raw25461step1 raw25461step1Labels := by
      have ha : raw25461step1 = (fun i j => raw25461step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25461step1 raw25461step0; decide +kernel
      have hl : raw25461step1Labels = raw25461step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25461step0 raw25461step0Labels permutation44 permutation3
    _ = mixedMoment B node985 node985Labels := by rfl

def raw25462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25462step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25462 raw25462Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw25462 raw25462Labels = mixedMoment B raw25462step0 raw25462step0Labels := by
      have hz : ∀ j, raw25462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25462step0 = (fun i j => raw25462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25462step0 raw25462; decide +kernel
      have hl : raw25462step0Labels = raw25462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25462 raw25462Labels permutation346 hz
    mixedMoment B raw25462step0 raw25462step0Labels = mixedMoment B raw25462step1 raw25462step1Labels := by
      have ha : raw25462step1 = (fun i j => raw25462step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25462step1 raw25462step0; decide +kernel
      have hl : raw25462step1Labels = raw25462step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25462step0 raw25462step0Labels permutation35 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw25463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25463step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25463 raw25463Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw25463 raw25463Labels = mixedMoment B raw25463step0 raw25463step0Labels := by
      have hz : ∀ j, raw25463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25463step0 = (fun i j => raw25463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25463step0 raw25463; decide +kernel
      have hl : raw25463step0Labels = raw25463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25463 raw25463Labels permutation346 hz
    mixedMoment B raw25463step0 raw25463step0Labels = mixedMoment B raw25463step1 raw25463step1Labels := by
      have ha : raw25463step1 = (fun i j => raw25463step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25463step1 raw25463step0; decide +kernel
      have hl : raw25463step1Labels = raw25463step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25463step0 raw25463step0Labels permutation32 permutation3
    _ = mixedMoment B node539 node539Labels := by rfl

def raw25464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25464step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25464step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25464 raw25464Labels = mixedMoment B node927 node927Labels := by
  calc
    mixedMoment B raw25464 raw25464Labels = mixedMoment B raw25464step0 raw25464step0Labels := by
      have hz : ∀ j, raw25464 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25464step0 = (fun i j => raw25464 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25464step0 raw25464; decide +kernel
      have hl : raw25464step0Labels = raw25464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25464 raw25464Labels permutation346 hz
    mixedMoment B raw25464step0 raw25464step0Labels = mixedMoment B raw25464step1 raw25464step1Labels := by
      have ha : raw25464step1 = (fun i j => raw25464step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25464step1 raw25464step0; decide +kernel
      have hl : raw25464step1Labels = raw25464step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25464step0 raw25464step0Labels permutation32 permutation3
    _ = mixedMoment B node927 node927Labels := by rfl

def raw25465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25465 raw25465Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw25465 raw25465Labels = mixedMoment B raw25465step0 raw25465step0Labels := by
      have ha : raw25465step0 = (fun i j => raw25465 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25465step0 raw25465; decide +kernel
      have hl : raw25465step0Labels = raw25465Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25465 raw25465Labels permutation176 permutation3
    _ = mixedMoment B node866 node866Labels := by rfl

def raw25466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25466step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25466 raw25466Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw25466 raw25466Labels = mixedMoment B raw25466step0 raw25466step0Labels := by
      have hz : ∀ j, raw25466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25466step0 = (fun i j => raw25466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25466step0 raw25466; decide +kernel
      have hl : raw25466step0Labels = raw25466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25466 raw25466Labels permutation346 hz
    mixedMoment B raw25466step0 raw25466step0Labels = mixedMoment B raw25466step1 raw25466step1Labels := by
      have ha : raw25466step1 = (fun i j => raw25466step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25466step1 raw25466step0; decide +kernel
      have hl : raw25466step1Labels = raw25466step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25466step0 raw25466step0Labels permutation33 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw25467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25467step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25467step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25467 raw25467Labels = mixedMoment B node536 node536Labels := by
  calc
    mixedMoment B raw25467 raw25467Labels = mixedMoment B raw25467step0 raw25467step0Labels := by
      have hz : ∀ j, raw25467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25467step0 = (fun i j => raw25467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25467step0 raw25467; decide +kernel
      have hl : raw25467step0Labels = raw25467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25467 raw25467Labels permutation346 hz
    mixedMoment B raw25467step0 raw25467step0Labels = mixedMoment B raw25467step1 raw25467step1Labels := by
      have ha : raw25467step1 = (fun i j => raw25467step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25467step1 raw25467step0; decide +kernel
      have hl : raw25467step1Labels = raw25467step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25467step0 raw25467step0Labels permutation32 permutation3
    _ = mixedMoment B node536 node536Labels := by rfl

def raw25468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25468 raw25468Labels = mixedMoment B node921 node921Labels := by
  calc
    mixedMoment B raw25468 raw25468Labels = mixedMoment B raw25468step0 raw25468step0Labels := by
      have hz : ∀ j, raw25468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25468step0 = (fun i j => raw25468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25468step0 raw25468; decide +kernel
      have hl : raw25468step0Labels = raw25468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25468 raw25468Labels permutation346 hz
    mixedMoment B raw25468step0 raw25468step0Labels = mixedMoment B raw25468step1 raw25468step1Labels := by
      have ha : raw25468step1 = (fun i j => raw25468step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25468step1 raw25468step0; decide +kernel
      have hl : raw25468step1Labels = raw25468step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25468step0 raw25468step0Labels permutation32 permutation3
    _ = mixedMoment B node921 node921Labels := by rfl

def raw25469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25469Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw25469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25469 raw25469Labels = mixedMoment B node864 node864Labels := by
  calc
    mixedMoment B raw25469 raw25469Labels = mixedMoment B raw25469step0 raw25469step0Labels := by
      have ha : raw25469step0 = (fun i j => raw25469 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25469step0 raw25469; decide +kernel
      have hl : raw25469step0Labels = raw25469Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25469 raw25469Labels permutation176 permutation3
    _ = mixedMoment B node864 node864Labels := by rfl

def raw25470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25470Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25470step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw25470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25470 raw25470Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw25470 raw25470Labels = mixedMoment B raw25470step0 raw25470step0Labels := by
      have hz : ∀ j, raw25470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25470step0 = (fun i j => raw25470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25470step0 raw25470; decide +kernel
      have hl : raw25470step0Labels = raw25470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25470 raw25470Labels permutation346 hz
    mixedMoment B raw25470step0 raw25470step0Labels = mixedMoment B raw25470step1 raw25470step1Labels := by
      have ha : raw25470step1 = (fun i j => raw25470step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25470step1 raw25470step0; decide +kernel
      have hl : raw25470step1Labels = raw25470step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25470step0 raw25470step0Labels permutation44 permutation3
    _ = mixedMoment B node979 node979Labels := by rfl

def raw25471 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw25471step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25471step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25471step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25471step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25471 raw25471Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw25471 raw25471Labels = mixedMoment B raw25471step0 raw25471step0Labels := by
      have hz : ∀ j, raw25471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25471step0 = (fun i j => raw25471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25471step0 raw25471; decide +kernel
      have hl : raw25471step0Labels = raw25471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25471 raw25471Labels permutation346 hz
    mixedMoment B raw25471step0 raw25471step0Labels = mixedMoment B raw25471step1 raw25471step1Labels := by
      have ha : raw25471step1 = (fun i j => raw25471step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25471step1 raw25471step0; decide +kernel
      have hl : raw25471step1Labels = raw25471step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25471step0 raw25471step0Labels permutation40 permutation4
    mixedMoment B raw25471step1 raw25471step1Labels = mixedMoment B raw25471step2 raw25471step2Labels := by
      have ha : raw25471step2 = -raw25471step1 := by apply Matrix.ext; change ∀ i j, raw25471step2 i j = -(raw25471step1 i j); unfold raw25471step2 raw25471step1; decide +kernel
      have hl : raw25471step2Labels = raw25471step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25471step2 raw25471step2Labels = mixedMoment B raw25471step3 raw25471step3Labels := by
      have ha : raw25471step3 = raw25471step2 := by apply Matrix.ext; unfold raw25471step3 raw25471step2; decide +kernel
      have hl : raw25471step2Labels = labelEmbedding7 ∘ raw25471step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25471step2 raw25471step2Labels raw25471step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
