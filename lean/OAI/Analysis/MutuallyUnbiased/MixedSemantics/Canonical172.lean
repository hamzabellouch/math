import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22016 raw22016Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw22016 raw22016Labels = mixedMoment B raw22016step0 raw22016step0Labels := by
      have hz : ∀ j, raw22016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22016step0 = (fun i j => raw22016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22016step0 raw22016; decide +kernel
      have hl : raw22016step0Labels = raw22016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22016 raw22016Labels permutation434 hz
    mixedMoment B raw22016step0 raw22016step0Labels = mixedMoment B raw22016step1 raw22016step1Labels := by
      have hz : ∀ j, raw22016step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22016step1 = (fun i j => raw22016step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22016step1 raw22016step0; decide +kernel
      have hl : raw22016step1Labels = raw22016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22016step0 raw22016step0Labels permutation80 hz
    _ = mixedMoment B node1740 node1740Labels := by rfl

def raw22017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22017 raw22017Labels = mixedMoment B node858 node858Labels := by
  calc
    mixedMoment B raw22017 raw22017Labels = mixedMoment B raw22017step0 raw22017step0Labels := by
      have hz : ∀ j, raw22017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22017step0 = (fun i j => raw22017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22017step0 raw22017; decide +kernel
      have hl : raw22017step0Labels = raw22017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22017 raw22017Labels permutation434 hz
    mixedMoment B raw22017step0 raw22017step0Labels = mixedMoment B raw22017step1 raw22017step1Labels := by
      have hz : ∀ j, raw22017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22017step1 = (fun i j => raw22017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22017step1 raw22017step0; decide +kernel
      have hl : raw22017step1Labels = raw22017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22017step0 raw22017step0Labels permutation80 hz
    _ = mixedMoment B node858 node858Labels := by rfl

def raw22018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22018 raw22018Labels = mixedMoment B node825 node825Labels := by
  calc
    mixedMoment B raw22018 raw22018Labels = mixedMoment B raw22018step0 raw22018step0Labels := by
      have hz : ∀ j, raw22018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22018step0 = (fun i j => raw22018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22018step0 raw22018; decide +kernel
      have hl : raw22018step0Labels = raw22018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22018 raw22018Labels permutation434 hz
    _ = mixedMoment B node825 node825Labels := by rfl

def raw22019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22019 raw22019Labels = mixedMoment B node825 node825Labels := by
  calc
    mixedMoment B raw22019 raw22019Labels = mixedMoment B raw22019step0 raw22019step0Labels := by
      have hz : ∀ j, raw22019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22019step0 = (fun i j => raw22019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22019step0 raw22019; decide +kernel
      have hl : raw22019step0Labels = raw22019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22019 raw22019Labels permutation346 hz
    _ = mixedMoment B node825 node825Labels := by rfl

def raw22020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, 0, -2], ![2, -2, 0]]
def raw22020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22020step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22020 raw22020Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw22020 raw22020Labels = mixedMoment B raw22020step0 raw22020step0Labels := by
      have hz : ∀ j, raw22020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22020step0 = (fun i j => raw22020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22020step0 raw22020; decide +kernel
      have hl : raw22020step0Labels = raw22020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22020 raw22020Labels permutation434 hz
    mixedMoment B raw22020step0 raw22020step0Labels = mixedMoment B raw22020step1 raw22020step1Labels := by
      have hz : ∀ j, raw22020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22020step1 = (fun i j => raw22020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22020step1 raw22020step0; decide +kernel
      have hl : raw22020step1Labels = raw22020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22020step0 raw22020step0Labels permutation80 hz
    mixedMoment B raw22020step1 raw22020step1Labels = mixedMoment B raw22020step2 raw22020step2Labels := by
      have ha : raw22020step2 = (fun i j => raw22020step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22020step2 raw22020step1; decide +kernel
      have hl : raw22020step2Labels = raw22020step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22020step1 raw22020step1Labels permutation9 permutation2
    _ = mixedMoment B node830 node830Labels := by rfl

def raw22021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw22021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22021 raw22021Labels = mixedMoment B node829 node829Labels := by
  calc
    mixedMoment B raw22021 raw22021Labels = mixedMoment B raw22021step0 raw22021step0Labels := by
      have hz : ∀ j, raw22021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22021step0 = (fun i j => raw22021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22021step0 raw22021; decide +kernel
      have hl : raw22021step0Labels = raw22021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22021 raw22021Labels permutation434 hz
    mixedMoment B raw22021step0 raw22021step0Labels = mixedMoment B raw22021step1 raw22021step1Labels := by
      have hz : ∀ j, raw22021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22021step1 = (fun i j => raw22021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22021step1 raw22021step0; decide +kernel
      have hl : raw22021step1Labels = raw22021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22021step0 raw22021step0Labels permutation80 hz
    _ = mixedMoment B node829 node829Labels := by rfl

def raw22022 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![2, -2], ![0, 0]]
def raw22022Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22022step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![2, -2]]
def raw22022step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22022step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![2, -2]]
def raw22022step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22022step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22022step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22022 raw22022Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw22022 raw22022Labels = mixedMoment B raw22022step0 raw22022step0Labels := by
      have hz : ∀ j, raw22022 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw22022step0 = (fun i j => raw22022 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw22022step0 raw22022; decide +kernel
      have hl : raw22022step0Labels = raw22022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22022 raw22022Labels permutation590 hz
    mixedMoment B raw22022step0 raw22022step0Labels = mixedMoment B raw22022step1 raw22022step1Labels := by
      have hz : ∀ j, raw22022step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22022step1 = (fun i j => raw22022step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22022step1 raw22022step0; decide +kernel
      have hl : raw22022step1Labels = raw22022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22022step0 raw22022step0Labels permutation104 hz
    mixedMoment B raw22022step1 raw22022step1Labels = mixedMoment B raw22022step2 raw22022step2Labels := by
      have hz : ∀ j, raw22022step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22022step2 = (fun i j => raw22022step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22022step2 raw22022step1; decide +kernel
      have hl : raw22022step2Labels = raw22022step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22022step1 raw22022step1Labels permutation20 hz
    _ = mixedMoment B node4071 node4071Labels := by rfl

def raw22023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw22023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22023 raw22023Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw22023 raw22023Labels = mixedMoment B raw22023step0 raw22023step0Labels := by
      have hz : ∀ j, raw22023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22023step0 = (fun i j => raw22023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22023step0 raw22023; decide +kernel
      have hl : raw22023step0Labels = raw22023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22023 raw22023Labels permutation434 hz
    mixedMoment B raw22023step0 raw22023step0Labels = mixedMoment B raw22023step1 raw22023step1Labels := by
      have hz : ∀ j, raw22023step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22023step1 = (fun i j => raw22023step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22023step1 raw22023step0; decide +kernel
      have hl : raw22023step1Labels = raw22023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22023step0 raw22023step0Labels permutation80 hz
    _ = mixedMoment B node828 node828Labels := by rfl

def raw22024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def raw22024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22024 raw22024Labels = mixedMoment B node1659 node1659Labels := by
  calc
    mixedMoment B raw22024 raw22024Labels = mixedMoment B raw22024step0 raw22024step0Labels := by
      have hz : ∀ j, raw22024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22024step0 = (fun i j => raw22024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22024step0 raw22024; decide +kernel
      have hl : raw22024step0Labels = raw22024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22024 raw22024Labels permutation434 hz
    mixedMoment B raw22024step0 raw22024step0Labels = mixedMoment B raw22024step1 raw22024step1Labels := by
      have hz : ∀ j, raw22024step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22024step1 = (fun i j => raw22024step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22024step1 raw22024step0; decide +kernel
      have hl : raw22024step1Labels = raw22024step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22024step0 raw22024step0Labels permutation80 hz
    _ = mixedMoment B node1659 node1659Labels := by rfl

def raw22025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw22025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22025 raw22025Labels = mixedMoment B node1610 node1610Labels := by
  calc
    mixedMoment B raw22025 raw22025Labels = mixedMoment B raw22025step0 raw22025step0Labels := by
      have hz : ∀ j, raw22025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22025step0 = (fun i j => raw22025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22025step0 raw22025; decide +kernel
      have hl : raw22025step0Labels = raw22025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22025 raw22025Labels permutation434 hz
    mixedMoment B raw22025step0 raw22025step0Labels = mixedMoment B raw22025step1 raw22025step1Labels := by
      have ha : raw22025step1 = (fun i j => raw22025step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22025step1 raw22025step0; decide +kernel
      have hl : raw22025step1Labels = raw22025step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22025step0 raw22025step0Labels permutation38 permutation2
    _ = mixedMoment B node1610 node1610Labels := by rfl

def raw22026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw22026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22026 raw22026Labels = mixedMoment B node1610 node1610Labels := by
  calc
    mixedMoment B raw22026 raw22026Labels = mixedMoment B raw22026step0 raw22026step0Labels := by
      have hz : ∀ j, raw22026 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22026step0 = (fun i j => raw22026 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22026step0 raw22026; decide +kernel
      have hl : raw22026step0Labels = raw22026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22026 raw22026Labels permutation346 hz
    mixedMoment B raw22026step0 raw22026step0Labels = mixedMoment B raw22026step1 raw22026step1Labels := by
      have ha : raw22026step1 = (fun i j => raw22026step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22026step1 raw22026step0; decide +kernel
      have hl : raw22026step1Labels = raw22026step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22026step0 raw22026step0Labels permutation38 permutation2
    _ = mixedMoment B node1610 node1610Labels := by rfl

def raw22027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![3, -2, -1]]
def raw22027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw22027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22027 raw22027Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw22027 raw22027Labels = mixedMoment B raw22027step0 raw22027step0Labels := by
      have hz : ∀ j, raw22027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22027step0 = (fun i j => raw22027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22027step0 raw22027; decide +kernel
      have hl : raw22027step0Labels = raw22027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22027 raw22027Labels permutation434 hz
    mixedMoment B raw22027step0 raw22027step0Labels = mixedMoment B raw22027step1 raw22027step1Labels := by
      have hz : ∀ j, raw22027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22027step1 = (fun i j => raw22027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22027step1 raw22027step0; decide +kernel
      have hl : raw22027step1Labels = raw22027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22027step0 raw22027step0Labels permutation80 hz
    mixedMoment B raw22027step1 raw22027step1Labels = mixedMoment B raw22027step2 raw22027step2Labels := by
      have ha : raw22027step2 = (fun i j => raw22027step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22027step2 raw22027step1; decide +kernel
      have hl : raw22027step2Labels = raw22027step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22027step1 raw22027step1Labels permutation10 permutation2
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw22028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22028 raw22028Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw22028 raw22028Labels = mixedMoment B raw22028step0 raw22028step0Labels := by
      have hz : ∀ j, raw22028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22028step0 = (fun i j => raw22028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22028step0 raw22028; decide +kernel
      have hl : raw22028step0Labels = raw22028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22028 raw22028Labels permutation434 hz
    mixedMoment B raw22028step0 raw22028step0Labels = mixedMoment B raw22028step1 raw22028step1Labels := by
      have hz : ∀ j, raw22028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22028step1 = (fun i j => raw22028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22028step1 raw22028step0; decide +kernel
      have hl : raw22028step1Labels = raw22028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22028step0 raw22028step0Labels permutation80 hz
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw22029 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]
def raw22029Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22029step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![1, -1], ![1, -1]]
def raw22029step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22029step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw22029step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22029step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22029step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22029 raw22029Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22029 raw22029Labels = mixedMoment B raw22029step0 raw22029step0Labels := by
      have hz : ∀ j, raw22029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22029step0 = (fun i j => raw22029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22029step0 raw22029; decide +kernel
      have hl : raw22029step0Labels = raw22029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22029 raw22029Labels permutation434 hz
    mixedMoment B raw22029step0 raw22029step0Labels = mixedMoment B raw22029step1 raw22029step1Labels := by
      have hz : ∀ j, raw22029step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22029step1 = (fun i j => raw22029step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22029step1 raw22029step0; decide +kernel
      have hl : raw22029step1Labels = raw22029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22029step0 raw22029step0Labels permutation80 hz
    mixedMoment B raw22029step1 raw22029step1Labels = mixedMoment B raw22029step2 raw22029step2Labels := by
      have ha : raw22029step2 = (fun i j => raw22029step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22029step2 raw22029step1; decide +kernel
      have hl : raw22029step2Labels = raw22029step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22029step1 raw22029step1Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw22030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22030step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw22030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22030step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22030step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22030 raw22030Labels = mixedMoment B node559 node559Labels := by
  calc
    mixedMoment B raw22030 raw22030Labels = mixedMoment B raw22030step0 raw22030step0Labels := by
      have hz : ∀ j, raw22030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22030step0 = (fun i j => raw22030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22030step0 raw22030; decide +kernel
      have hl : raw22030step0Labels = raw22030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22030 raw22030Labels permutation434 hz
    mixedMoment B raw22030step0 raw22030step0Labels = mixedMoment B raw22030step1 raw22030step1Labels := by
      have hz : ∀ j, raw22030step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22030step1 = (fun i j => raw22030step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22030step1 raw22030step0; decide +kernel
      have hl : raw22030step1Labels = raw22030step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22030step0 raw22030step0Labels permutation80 hz
    mixedMoment B raw22030step1 raw22030step1Labels = mixedMoment B raw22030step2 raw22030step2Labels := by
      have ha : raw22030step2 = (fun i j => raw22030step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22030step2 raw22030step1; decide +kernel
      have hl : raw22030step2Labels = raw22030step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22030step1 raw22030step1Labels permutation10 permutation2
    _ = mixedMoment B node559 node559Labels := by rfl

def raw22031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22031 raw22031Labels = mixedMoment B node720 node720Labels := by
  calc
    mixedMoment B raw22031 raw22031Labels = mixedMoment B raw22031step0 raw22031step0Labels := by
      have hz : ∀ j, raw22031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22031step0 = (fun i j => raw22031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22031step0 raw22031; decide +kernel
      have hl : raw22031step0Labels = raw22031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22031 raw22031Labels permutation434 hz
    mixedMoment B raw22031step0 raw22031step0Labels = mixedMoment B raw22031step1 raw22031step1Labels := by
      have ha : raw22031step1 = (fun i j => raw22031step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22031step1 raw22031step0; decide +kernel
      have hl : raw22031step1Labels = raw22031step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22031step0 raw22031step0Labels permutation40 permutation2
    _ = mixedMoment B node720 node720Labels := by rfl

def raw22032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22032 raw22032Labels = mixedMoment B node720 node720Labels := by
  calc
    mixedMoment B raw22032 raw22032Labels = mixedMoment B raw22032step0 raw22032step0Labels := by
      have hz : ∀ j, raw22032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22032step0 = (fun i j => raw22032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22032step0 raw22032; decide +kernel
      have hl : raw22032step0Labels = raw22032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22032 raw22032Labels permutation346 hz
    mixedMoment B raw22032step0 raw22032step0Labels = mixedMoment B raw22032step1 raw22032step1Labels := by
      have ha : raw22032step1 = (fun i j => raw22032step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22032step1 raw22032step0; decide +kernel
      have hl : raw22032step1Labels = raw22032step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22032step0 raw22032step0Labels permutation40 permutation2
    _ = mixedMoment B node720 node720Labels := by rfl

def raw22033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 1, -1], ![3, -2, -1]]
def raw22033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22033step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22033 raw22033Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw22033 raw22033Labels = mixedMoment B raw22033step0 raw22033step0Labels := by
      have hz : ∀ j, raw22033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22033step0 = (fun i j => raw22033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22033step0 raw22033; decide +kernel
      have hl : raw22033step0Labels = raw22033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22033 raw22033Labels permutation434 hz
    mixedMoment B raw22033step0 raw22033step0Labels = mixedMoment B raw22033step1 raw22033step1Labels := by
      have hz : ∀ j, raw22033step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22033step1 = (fun i j => raw22033step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22033step1 raw22033step0; decide +kernel
      have hl : raw22033step1Labels = raw22033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22033step0 raw22033step0Labels permutation80 hz
    mixedMoment B raw22033step1 raw22033step1Labels = mixedMoment B raw22033step2 raw22033step2Labels := by
      have ha : raw22033step2 = (fun i j => raw22033step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22033step2 raw22033step1; decide +kernel
      have hl : raw22033step2Labels = raw22033step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22033step1 raw22033step1Labels permutation10 permutation2
    _ = mixedMoment B node813 node813Labels := by rfl

def raw22034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22034 raw22034Labels = mixedMoment B node856 node856Labels := by
  calc
    mixedMoment B raw22034 raw22034Labels = mixedMoment B raw22034step0 raw22034step0Labels := by
      have hz : ∀ j, raw22034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22034step0 = (fun i j => raw22034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22034step0 raw22034; decide +kernel
      have hl : raw22034step0Labels = raw22034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22034 raw22034Labels permutation434 hz
    mixedMoment B raw22034step0 raw22034step0Labels = mixedMoment B raw22034step1 raw22034step1Labels := by
      have hz : ∀ j, raw22034step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22034step1 = (fun i j => raw22034step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22034step1 raw22034step0; decide +kernel
      have hl : raw22034step1Labels = raw22034step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22034step0 raw22034step0Labels permutation80 hz
    mixedMoment B raw22034step1 raw22034step1Labels = mixedMoment B raw22034step2 raw22034step2Labels := by
      have ha : raw22034step2 = (fun i j => raw22034step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22034step2 raw22034step1; decide +kernel
      have hl : raw22034step2Labels = raw22034step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22034step1 raw22034step1Labels permutation10 permutation2
    _ = mixedMoment B node856 node856Labels := by rfl

def raw22035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22035 raw22035Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw22035 raw22035Labels = mixedMoment B raw22035step0 raw22035step0Labels := by
      have hz : ∀ j, raw22035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22035step0 = (fun i j => raw22035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22035step0 raw22035; decide +kernel
      have hl : raw22035step0Labels = raw22035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22035 raw22035Labels permutation434 hz
    _ = mixedMoment B node824 node824Labels := by rfl

def raw22036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22036 raw22036Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw22036 raw22036Labels = mixedMoment B raw22036step0 raw22036step0Labels := by
      have hz : ∀ j, raw22036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22036step0 = (fun i j => raw22036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22036step0 raw22036; decide +kernel
      have hl : raw22036step0Labels = raw22036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22036 raw22036Labels permutation346 hz
    _ = mixedMoment B node824 node824Labels := by rfl

def raw22037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw22037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22037 raw22037Labels = mixedMoment B node831 node831Labels := by
  calc
    mixedMoment B raw22037 raw22037Labels = mixedMoment B raw22037step0 raw22037step0Labels := by
      have hz : ∀ j, raw22037 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22037step0 = (fun i j => raw22037 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22037step0 raw22037; decide +kernel
      have hl : raw22037step0Labels = raw22037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22037 raw22037Labels permutation434 hz
    mixedMoment B raw22037step0 raw22037step0Labels = mixedMoment B raw22037step1 raw22037step1Labels := by
      have hz : ∀ j, raw22037step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22037step1 = (fun i j => raw22037step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22037step1 raw22037step0; decide +kernel
      have hl : raw22037step1Labels = raw22037step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22037step0 raw22037step0Labels permutation80 hz
    _ = mixedMoment B node831 node831Labels := by rfl

def raw22038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22038step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22038 raw22038Labels = mixedMoment B node560 node560Labels := by
  calc
    mixedMoment B raw22038 raw22038Labels = mixedMoment B raw22038step0 raw22038step0Labels := by
      have hz : ∀ j, raw22038 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22038step0 = (fun i j => raw22038 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22038step0 raw22038; decide +kernel
      have hl : raw22038step0Labels = raw22038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22038 raw22038Labels permutation434 hz
    mixedMoment B raw22038step0 raw22038step0Labels = mixedMoment B raw22038step1 raw22038step1Labels := by
      have hz : ∀ j, raw22038step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22038step1 = (fun i j => raw22038step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22038step1 raw22038step0; decide +kernel
      have hl : raw22038step1Labels = raw22038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22038step0 raw22038step0Labels permutation80 hz
    mixedMoment B raw22038step1 raw22038step1Labels = mixedMoment B raw22038step2 raw22038step2Labels := by
      have ha : raw22038step2 = (fun i j => raw22038step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22038step2 raw22038step1; decide +kernel
      have hl : raw22038step2Labels = raw22038step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22038step1 raw22038step1Labels permutation10 permutation4
    mixedMoment B raw22038step2 raw22038step2Labels = mixedMoment B raw22038step3 raw22038step3Labels := by
      have ha : raw22038step3 = -raw22038step2 := by apply Matrix.ext; change ∀ i j, raw22038step3 i j = -(raw22038step2 i j); unfold raw22038step3 raw22038step2; decide +kernel
      have hl : raw22038step3Labels = raw22038step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node560 node560Labels := by rfl

def raw22039 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22039step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22039 raw22039Labels = mixedMoment B node721 node721Labels := by
  calc
    mixedMoment B raw22039 raw22039Labels = mixedMoment B raw22039step0 raw22039step0Labels := by
      have hz : ∀ j, raw22039 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22039step0 = (fun i j => raw22039 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22039step0 raw22039; decide +kernel
      have hl : raw22039step0Labels = raw22039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22039 raw22039Labels permutation434 hz
    mixedMoment B raw22039step0 raw22039step0Labels = mixedMoment B raw22039step1 raw22039step1Labels := by
      have ha : raw22039step1 = (fun i j => raw22039step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22039step1 raw22039step0; decide +kernel
      have hl : raw22039step1Labels = raw22039step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22039step0 raw22039step0Labels permutation40 permutation4
    mixedMoment B raw22039step1 raw22039step1Labels = mixedMoment B raw22039step2 raw22039step2Labels := by
      have ha : raw22039step2 = -raw22039step1 := by apply Matrix.ext; change ∀ i j, raw22039step2 i j = -(raw22039step1 i j); unfold raw22039step2 raw22039step1; decide +kernel
      have hl : raw22039step2Labels = raw22039step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node721 node721Labels := by rfl

def raw22040 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22040step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22040step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22040 raw22040Labels = mixedMoment B node815 node815Labels := by
  calc
    mixedMoment B raw22040 raw22040Labels = mixedMoment B raw22040step0 raw22040step0Labels := by
      have hz : ∀ j, raw22040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22040step0 = (fun i j => raw22040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22040step0 raw22040; decide +kernel
      have hl : raw22040step0Labels = raw22040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22040 raw22040Labels permutation434 hz
    mixedMoment B raw22040step0 raw22040step0Labels = mixedMoment B raw22040step1 raw22040step1Labels := by
      have hz : ∀ j, raw22040step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22040step1 = (fun i j => raw22040step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22040step1 raw22040step0; decide +kernel
      have hl : raw22040step1Labels = raw22040step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22040step0 raw22040step0Labels permutation80 hz
    mixedMoment B raw22040step1 raw22040step1Labels = mixedMoment B raw22040step2 raw22040step2Labels := by
      have ha : raw22040step2 = (fun i j => raw22040step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22040step2 raw22040step1; decide +kernel
      have hl : raw22040step2Labels = raw22040step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22040step1 raw22040step1Labels permutation10 permutation4
    mixedMoment B raw22040step2 raw22040step2Labels = mixedMoment B raw22040step3 raw22040step3Labels := by
      have ha : raw22040step3 = -raw22040step2 := by apply Matrix.ext; change ∀ i j, raw22040step3 i j = -(raw22040step2 i j); unfold raw22040step3 raw22040step2; decide +kernel
      have hl : raw22040step3Labels = raw22040step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node815 node815Labels := by rfl

def raw22041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22041 raw22041Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw22041 raw22041Labels = mixedMoment B raw22041step0 raw22041step0Labels := by
      have hz : ∀ j, raw22041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22041step0 = (fun i j => raw22041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22041step0 raw22041; decide +kernel
      have hl : raw22041step0Labels = raw22041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22041 raw22041Labels permutation434 hz
    mixedMoment B raw22041step0 raw22041step0Labels = mixedMoment B raw22041step1 raw22041step1Labels := by
      have hz : ∀ j, raw22041step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22041step1 = (fun i j => raw22041step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22041step1 raw22041step0; decide +kernel
      have hl : raw22041step1Labels = raw22041step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22041step0 raw22041step0Labels permutation80 hz
    _ = mixedMoment B node826 node826Labels := by rfl

def raw22042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22042 raw22042Labels = mixedMoment B node1657 node1657Labels := by
  calc
    mixedMoment B raw22042 raw22042Labels = mixedMoment B raw22042step0 raw22042step0Labels := by
      have hz : ∀ j, raw22042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22042step0 = (fun i j => raw22042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22042step0 raw22042; decide +kernel
      have hl : raw22042step0Labels = raw22042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22042 raw22042Labels permutation434 hz
    mixedMoment B raw22042step0 raw22042step0Labels = mixedMoment B raw22042step1 raw22042step1Labels := by
      have hz : ∀ j, raw22042step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22042step1 = (fun i j => raw22042step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22042step1 raw22042step0; decide +kernel
      have hl : raw22042step1Labels = raw22042step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22042step0 raw22042step0Labels permutation80 hz
    _ = mixedMoment B node1657 node1657Labels := by rfl

def raw22043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22043 raw22043Labels = mixedMoment B node1608 node1608Labels := by
  calc
    mixedMoment B raw22043 raw22043Labels = mixedMoment B raw22043step0 raw22043step0Labels := by
      have hz : ∀ j, raw22043 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22043step0 = (fun i j => raw22043 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22043step0 raw22043; decide +kernel
      have hl : raw22043step0Labels = raw22043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22043 raw22043Labels permutation434 hz
    mixedMoment B raw22043step0 raw22043step0Labels = mixedMoment B raw22043step1 raw22043step1Labels := by
      have ha : raw22043step1 = (fun i j => raw22043step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22043step1 raw22043step0; decide +kernel
      have hl : raw22043step1Labels = raw22043step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22043step0 raw22043step0Labels permutation38 permutation2
    _ = mixedMoment B node1608 node1608Labels := by rfl

def raw22044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22044 raw22044Labels = mixedMoment B node1608 node1608Labels := by
  calc
    mixedMoment B raw22044 raw22044Labels = mixedMoment B raw22044step0 raw22044step0Labels := by
      have hz : ∀ j, raw22044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22044step0 = (fun i j => raw22044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22044step0 raw22044; decide +kernel
      have hl : raw22044step0Labels = raw22044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22044 raw22044Labels permutation346 hz
    mixedMoment B raw22044step0 raw22044step0Labels = mixedMoment B raw22044step1 raw22044step1Labels := by
      have ha : raw22044step1 = (fun i j => raw22044step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22044step1 raw22044step0; decide +kernel
      have hl : raw22044step1Labels = raw22044step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22044step0 raw22044step0Labels permutation38 permutation2
    _ = mixedMoment B node1608 node1608Labels := by rfl

def raw22045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![3, -1, -2]]
def raw22045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22045step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw22045step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22045 raw22045Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw22045 raw22045Labels = mixedMoment B raw22045step0 raw22045step0Labels := by
      have hz : ∀ j, raw22045 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22045step0 = (fun i j => raw22045 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22045step0 raw22045; decide +kernel
      have hl : raw22045step0Labels = raw22045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22045 raw22045Labels permutation520 hz
    mixedMoment B raw22045step0 raw22045step0Labels = mixedMoment B raw22045step1 raw22045step1Labels := by
      have hz : ∀ j, raw22045step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22045step1 = (fun i j => raw22045step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22045step1 raw22045step0; decide +kernel
      have hl : raw22045step1Labels = raw22045step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22045step0 raw22045step0Labels permutation104 hz
    mixedMoment B raw22045step1 raw22045step1Labels = mixedMoment B raw22045step2 raw22045step2Labels := by
      have hz : ∀ j, raw22045step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22045step2 = (fun i j => raw22045step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22045step2 raw22045step1; decide +kernel
      have hl : raw22045step2Labels = raw22045step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22045step1 raw22045step1Labels permutation20 hz
    _ = mixedMoment B node1741 node1741Labels := by rfl

def raw22046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22046 raw22046Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw22046 raw22046Labels = mixedMoment B raw22046step0 raw22046step0Labels := by
      have hz : ∀ j, raw22046 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22046step0 = (fun i j => raw22046 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22046step0 raw22046; decide +kernel
      have hl : raw22046step0Labels = raw22046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22046 raw22046Labels permutation434 hz
    mixedMoment B raw22046step0 raw22046step0Labels = mixedMoment B raw22046step1 raw22046step1Labels := by
      have hz : ∀ j, raw22046step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22046step1 = (fun i j => raw22046step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22046step1 raw22046step0; decide +kernel
      have hl : raw22046step1Labels = raw22046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22046step0 raw22046step0Labels permutation80 hz
    _ = mixedMoment B node1738 node1738Labels := by rfl

def raw22047 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]
def raw22047Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22047step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![0, 0], ![2, -2]]
def raw22047step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22047step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![2, -2]]
def raw22047step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22047step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22047step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22047 raw22047Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw22047 raw22047Labels = mixedMoment B raw22047step0 raw22047step0Labels := by
      have hz : ∀ j, raw22047 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22047step0 = (fun i j => raw22047 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22047step0 raw22047; decide +kernel
      have hl : raw22047step0Labels = raw22047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22047 raw22047Labels permutation520 hz
    mixedMoment B raw22047step0 raw22047step0Labels = mixedMoment B raw22047step1 raw22047step1Labels := by
      have hz : ∀ j, raw22047step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22047step1 = (fun i j => raw22047step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22047step1 raw22047step0; decide +kernel
      have hl : raw22047step1Labels = raw22047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22047step0 raw22047step0Labels permutation104 hz
    mixedMoment B raw22047step1 raw22047step1Labels = mixedMoment B raw22047step2 raw22047step2Labels := by
      have hz : ∀ j, raw22047step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22047step2 = (fun i j => raw22047step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22047step2 raw22047step1; decide +kernel
      have hl : raw22047step2Labels = raw22047step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22047step1 raw22047step1Labels permutation20 hz
    _ = mixedMoment B node4071 node4071Labels := by rfl

def raw22048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22048step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22048 raw22048Labels = mixedMoment B node555 node555Labels := by
  calc
    mixedMoment B raw22048 raw22048Labels = mixedMoment B raw22048step0 raw22048step0Labels := by
      have hz : ∀ j, raw22048 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22048step0 = (fun i j => raw22048 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22048step0 raw22048; decide +kernel
      have hl : raw22048step0Labels = raw22048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22048 raw22048Labels permutation434 hz
    mixedMoment B raw22048step0 raw22048step0Labels = mixedMoment B raw22048step1 raw22048step1Labels := by
      have hz : ∀ j, raw22048step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22048step1 = (fun i j => raw22048step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22048step1 raw22048step0; decide +kernel
      have hl : raw22048step1Labels = raw22048step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22048step0 raw22048step0Labels permutation80 hz
    mixedMoment B raw22048step1 raw22048step1Labels = mixedMoment B raw22048step2 raw22048step2Labels := by
      have ha : raw22048step2 = (fun i j => raw22048step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22048step2 raw22048step1; decide +kernel
      have hl : raw22048step2Labels = raw22048step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22048step1 raw22048step1Labels permutation10 permutation2
    _ = mixedMoment B node555 node555Labels := by rfl

def raw22049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22049 raw22049Labels = mixedMoment B node715 node715Labels := by
  calc
    mixedMoment B raw22049 raw22049Labels = mixedMoment B raw22049step0 raw22049step0Labels := by
      have hz : ∀ j, raw22049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22049step0 = (fun i j => raw22049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22049step0 raw22049; decide +kernel
      have hl : raw22049step0Labels = raw22049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22049 raw22049Labels permutation434 hz
    mixedMoment B raw22049step0 raw22049step0Labels = mixedMoment B raw22049step1 raw22049step1Labels := by
      have ha : raw22049step1 = (fun i j => raw22049step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22049step1 raw22049step0; decide +kernel
      have hl : raw22049step1Labels = raw22049step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22049step0 raw22049step0Labels permutation40 permutation2
    _ = mixedMoment B node715 node715Labels := by rfl

def raw22050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22050 raw22050Labels = mixedMoment B node715 node715Labels := by
  calc
    mixedMoment B raw22050 raw22050Labels = mixedMoment B raw22050step0 raw22050step0Labels := by
      have hz : ∀ j, raw22050 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22050step0 = (fun i j => raw22050 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22050step0 raw22050; decide +kernel
      have hl : raw22050step0Labels = raw22050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22050 raw22050Labels permutation346 hz
    mixedMoment B raw22050step0 raw22050step0Labels = mixedMoment B raw22050step1 raw22050step1Labels := by
      have ha : raw22050step1 = (fun i j => raw22050step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22050step1 raw22050step0; decide +kernel
      have hl : raw22050step1Labels = raw22050step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22050step0 raw22050step0Labels permutation40 permutation2
    _ = mixedMoment B node715 node715Labels := by rfl

def raw22051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![3, -1, -2]]
def raw22051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22051step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def raw22051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22051 raw22051Labels = mixedMoment B node859 node859Labels := by
  calc
    mixedMoment B raw22051 raw22051Labels = mixedMoment B raw22051step0 raw22051step0Labels := by
      have hz : ∀ j, raw22051 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22051step0 = (fun i j => raw22051 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22051step0 raw22051; decide +kernel
      have hl : raw22051step0Labels = raw22051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22051 raw22051Labels permutation520 hz
    mixedMoment B raw22051step0 raw22051step0Labels = mixedMoment B raw22051step1 raw22051step1Labels := by
      have hz : ∀ j, raw22051step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22051step1 = (fun i j => raw22051step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22051step1 raw22051step0; decide +kernel
      have hl : raw22051step1Labels = raw22051step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22051step0 raw22051step0Labels permutation104 hz
    mixedMoment B raw22051step1 raw22051step1Labels = mixedMoment B raw22051step2 raw22051step2Labels := by
      have hz : ∀ j, raw22051step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22051step2 = (fun i j => raw22051step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22051step2 raw22051step1; decide +kernel
      have hl : raw22051step2Labels = raw22051step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22051step1 raw22051step1Labels permutation20 hz
    _ = mixedMoment B node859 node859Labels := by rfl

def raw22052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22052 raw22052Labels = mixedMoment B node852 node852Labels := by
  calc
    mixedMoment B raw22052 raw22052Labels = mixedMoment B raw22052step0 raw22052step0Labels := by
      have hz : ∀ j, raw22052 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22052step0 = (fun i j => raw22052 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22052step0 raw22052; decide +kernel
      have hl : raw22052step0Labels = raw22052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22052 raw22052Labels permutation434 hz
    mixedMoment B raw22052step0 raw22052step0Labels = mixedMoment B raw22052step1 raw22052step1Labels := by
      have hz : ∀ j, raw22052step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22052step1 = (fun i j => raw22052step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22052step1 raw22052step0; decide +kernel
      have hl : raw22052step1Labels = raw22052step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22052step0 raw22052step0Labels permutation80 hz
    mixedMoment B raw22052step1 raw22052step1Labels = mixedMoment B raw22052step2 raw22052step2Labels := by
      have ha : raw22052step2 = (fun i j => raw22052step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22052step2 raw22052step1; decide +kernel
      have hl : raw22052step2Labels = raw22052step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22052step1 raw22052step1Labels permutation10 permutation2
    _ = mixedMoment B node852 node852Labels := by rfl

def raw22053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22053 raw22053Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw22053 raw22053Labels = mixedMoment B raw22053step0 raw22053step0Labels := by
      have hz : ∀ j, raw22053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22053step0 = (fun i j => raw22053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22053step0 raw22053; decide +kernel
      have hl : raw22053step0Labels = raw22053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22053 raw22053Labels permutation434 hz
    _ = mixedMoment B node823 node823Labels := by rfl

def raw22054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22054 raw22054Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw22054 raw22054Labels = mixedMoment B raw22054step0 raw22054step0Labels := by
      have hz : ∀ j, raw22054 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22054step0 = (fun i j => raw22054 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22054step0 raw22054; decide +kernel
      have hl : raw22054step0Labels = raw22054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22054 raw22054Labels permutation346 hz
    _ = mixedMoment B node823 node823Labels := by rfl

def raw22055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22055 raw22055Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw22055 raw22055Labels = mixedMoment B raw22055step0 raw22055step0Labels := by
      have hz : ∀ j, raw22055 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22055step0 = (fun i j => raw22055 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22055step0 raw22055; decide +kernel
      have hl : raw22055step0Labels = raw22055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22055 raw22055Labels permutation434 hz
    mixedMoment B raw22055step0 raw22055step0Labels = mixedMoment B raw22055step1 raw22055step1Labels := by
      have hz : ∀ j, raw22055step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22055step1 = (fun i j => raw22055step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22055step1 raw22055step0; decide +kernel
      have hl : raw22055step1Labels = raw22055step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22055step0 raw22055step0Labels permutation80 hz
    _ = mixedMoment B node830 node830Labels := by rfl

def raw22056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw22056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22056step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22056step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22056 raw22056Labels = mixedMoment B node546 node546Labels := by
  calc
    mixedMoment B raw22056 raw22056Labels = mixedMoment B raw22056step0 raw22056step0Labels := by
      have hz : ∀ j, raw22056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22056step0 = (fun i j => raw22056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22056step0 raw22056; decide +kernel
      have hl : raw22056step0Labels = raw22056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22056 raw22056Labels permutation434 hz
    mixedMoment B raw22056step0 raw22056step0Labels = mixedMoment B raw22056step1 raw22056step1Labels := by
      have hz : ∀ j, raw22056step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22056step1 = (fun i j => raw22056step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22056step1 raw22056step0; decide +kernel
      have hl : raw22056step1Labels = raw22056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22056step0 raw22056step0Labels permutation80 hz
    mixedMoment B raw22056step1 raw22056step1Labels = mixedMoment B raw22056step2 raw22056step2Labels := by
      have ha : raw22056step2 = (fun i j => raw22056step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22056step2 raw22056step1; decide +kernel
      have hl : raw22056step2Labels = raw22056step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22056step1 raw22056step1Labels permutation10 permutation4
    mixedMoment B raw22056step2 raw22056step2Labels = mixedMoment B raw22056step3 raw22056step3Labels := by
      have ha : raw22056step3 = -raw22056step2 := by apply Matrix.ext; change ∀ i j, raw22056step3 i j = -(raw22056step2 i j); unfold raw22056step3 raw22056step2; decide +kernel
      have hl : raw22056step3Labels = raw22056step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node546 node546Labels := by rfl

def raw22057 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw22057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw22057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22057 raw22057Labels = mixedMoment B node706 node706Labels := by
  calc
    mixedMoment B raw22057 raw22057Labels = mixedMoment B raw22057step0 raw22057step0Labels := by
      have hz : ∀ j, raw22057 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22057step0 = (fun i j => raw22057 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22057step0 raw22057; decide +kernel
      have hl : raw22057step0Labels = raw22057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22057 raw22057Labels permutation434 hz
    mixedMoment B raw22057step0 raw22057step0Labels = mixedMoment B raw22057step1 raw22057step1Labels := by
      have ha : raw22057step1 = (fun i j => raw22057step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22057step1 raw22057step0; decide +kernel
      have hl : raw22057step1Labels = raw22057step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22057step0 raw22057step0Labels permutation40 permutation4
    mixedMoment B raw22057step1 raw22057step1Labels = mixedMoment B raw22057step2 raw22057step2Labels := by
      have ha : raw22057step2 = -raw22057step1 := by apply Matrix.ext; change ∀ i j, raw22057step2 i j = -(raw22057step1 i j); unfold raw22057step2 raw22057step1; decide +kernel
      have hl : raw22057step2Labels = raw22057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node706 node706Labels := by rfl

def raw22058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22058 raw22058Labels = mixedMoment B node1699 node1699Labels := by
  calc
    _ = mixedMoment B node1699 node1699Labels := by rfl

def raw22059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22059 raw22059Labels = mixedMoment B node786 node786Labels := by
  calc
    mixedMoment B raw22059 raw22059Labels = mixedMoment B raw22059step0 raw22059step0Labels := by
      have ha : raw22059step0 = (fun i j => raw22059 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22059step0 raw22059; decide +kernel
      have hl : raw22059step0Labels = raw22059Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22059 raw22059Labels permutation182 permutation2
    _ = mixedMoment B node786 node786Labels := by rfl

def raw22060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22060 raw22060Labels = mixedMoment B node786 node786Labels := by
  calc
    mixedMoment B raw22060 raw22060Labels = mixedMoment B raw22060step0 raw22060step0Labels := by
      have ha : raw22060step0 = (fun i j => raw22060 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22060step0 raw22060; decide +kernel
      have hl : raw22060step0Labels = raw22060Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22060 raw22060Labels permutation158 permutation2
    _ = mixedMoment B node786 node786Labels := by rfl

def raw22061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22061 raw22061Labels = mixedMoment B node786 node786Labels := by
  calc
    _ = mixedMoment B node786 node786Labels := by rfl

def raw22062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw22062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22062 raw22062Labels = mixedMoment B node778 node778Labels := by
  calc
    mixedMoment B raw22062 raw22062Labels = mixedMoment B raw22062step0 raw22062step0Labels := by
      have ha : raw22062step0 = (fun i j => raw22062 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22062step0 raw22062; decide +kernel
      have hl : raw22062step0Labels = raw22062Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22062 raw22062Labels permutation153 permutation2
    _ = mixedMoment B node778 node778Labels := by rfl

def raw22063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw22063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22063 raw22063Labels = mixedMoment B node777 node777Labels := by
  calc
    _ = mixedMoment B node777 node777Labels := by rfl

def raw22064 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw22064Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22064step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw22064step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22064 raw22064Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw22064 raw22064Labels = mixedMoment B raw22064step0 raw22064step0Labels := by
      have hz : ∀ j, raw22064 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw22064step0 = (fun i j => raw22064 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw22064step0 raw22064; decide +kernel
      have hl : raw22064step0Labels = raw22064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22064 raw22064Labels permutation590 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw22065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22065 raw22065Labels = mixedMoment B node1698 node1698Labels := by
  calc
    _ = mixedMoment B node1698 node1698Labels := by rfl

def raw22066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22066 raw22066Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw22066 raw22066Labels = mixedMoment B raw22066step0 raw22066step0Labels := by
      have ha : raw22066step0 = (fun i j => raw22066 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22066step0 raw22066; decide +kernel
      have hl : raw22066step0Labels = raw22066Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22066 raw22066Labels permutation184 permutation2
    _ = mixedMoment B node783 node783Labels := by rfl

def raw22067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22067 raw22067Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw22067 raw22067Labels = mixedMoment B raw22067step0 raw22067step0Labels := by
      have ha : raw22067step0 = (fun i j => raw22067 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22067step0 raw22067; decide +kernel
      have hl : raw22067step0Labels = raw22067Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22067 raw22067Labels permutation160 permutation2
    _ = mixedMoment B node783 node783Labels := by rfl

def raw22068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22068 raw22068Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw22068 raw22068Labels = mixedMoment B raw22068step0 raw22068step0Labels := by
      have ha : raw22068step0 = (fun i j => raw22068 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22068step0 raw22068; decide +kernel
      have hl : raw22068step0Labels = raw22068Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22068 raw22068Labels permutation154 permutation2
    _ = mixedMoment B node783 node783Labels := by rfl

def raw22069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22069 raw22069Labels = mixedMoment B node778 node778Labels := by
  calc
    _ = mixedMoment B node778 node778Labels := by rfl

def raw22070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw22070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22070 raw22070Labels = mixedMoment B node776 node776Labels := by
  calc
    _ = mixedMoment B node776 node776Labels := by rfl

def raw22071 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw22071Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22071step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw22071step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22071 raw22071Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw22071 raw22071Labels = mixedMoment B raw22071step0 raw22071step0Labels := by
      have hz : ∀ j, raw22071 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22071step0 = (fun i j => raw22071 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22071step0 raw22071; decide +kernel
      have hl : raw22071step0Labels = raw22071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22071 raw22071Labels permutation520 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw22072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22072 raw22072Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw22072 raw22072Labels = mixedMoment B raw22072step0 raw22072step0Labels := by
      have hz : ∀ j, raw22072 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22072step0 = (fun i j => raw22072 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22072step0 raw22072; decide +kernel
      have hl : raw22072step0Labels = raw22072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22072 raw22072Labels permutation434 hz
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw22073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22073 raw22073Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw22073 raw22073Labels = mixedMoment B raw22073step0 raw22073step0Labels := by
      have hz : ∀ j, raw22073 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22073step0 = (fun i j => raw22073 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22073step0 raw22073; decide +kernel
      have hl : raw22073step0Labels = raw22073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22073 raw22073Labels permutation434 hz
    mixedMoment B raw22073step0 raw22073step0Labels = mixedMoment B raw22073step1 raw22073step1Labels := by
      have ha : raw22073step1 = (fun i j => raw22073step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22073step1 raw22073step0; decide +kernel
      have hl : raw22073step1Labels = raw22073step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22073step0 raw22073step0Labels permutation38 permutation2
    _ = mixedMoment B node811 node811Labels := by rfl

def raw22074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22074 raw22074Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw22074 raw22074Labels = mixedMoment B raw22074step0 raw22074step0Labels := by
      have hz : ∀ j, raw22074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22074step0 = (fun i j => raw22074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22074step0 raw22074; decide +kernel
      have hl : raw22074step0Labels = raw22074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22074 raw22074Labels permutation434 hz
    _ = mixedMoment B node811 node811Labels := by rfl

def raw22075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22075 raw22075Labels = mixedMoment B node784 node784Labels := by
  calc
    _ = mixedMoment B node784 node784Labels := by rfl

def raw22076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw22076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw22076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22076 raw22076Labels = mixedMoment B node789 node789Labels := by
  calc
    mixedMoment B raw22076 raw22076Labels = mixedMoment B raw22076step0 raw22076step0Labels := by
      have hz : ∀ j, raw22076 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22076step0 = (fun i j => raw22076 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22076step0 raw22076; decide +kernel
      have hl : raw22076step0Labels = raw22076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22076 raw22076Labels permutation434 hz
    mixedMoment B raw22076step0 raw22076step0Labels = mixedMoment B raw22076step1 raw22076step1Labels := by
      have ha : raw22076step1 = (fun i j => raw22076step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22076step1 raw22076step0; decide +kernel
      have hl : raw22076step1Labels = raw22076step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22076step0 raw22076step0Labels permutation33 permutation2
    _ = mixedMoment B node789 node789Labels := by rfl

def raw22077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw22077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw22077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22077 raw22077Labels = mixedMoment B node788 node788Labels := by
  calc
    mixedMoment B raw22077 raw22077Labels = mixedMoment B raw22077step0 raw22077step0Labels := by
      have hz : ∀ j, raw22077 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22077step0 = (fun i j => raw22077 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22077step0 raw22077; decide +kernel
      have hl : raw22077step0Labels = raw22077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22077 raw22077Labels permutation434 hz
    _ = mixedMoment B node788 node788Labels := by rfl

def raw22078 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]
def raw22078Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22078step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]
def raw22078step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22078step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22078step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22078 raw22078Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22078 raw22078Labels = mixedMoment B raw22078step0 raw22078step0Labels := by
      have hz : ∀ j, raw22078 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw22078step0 = (fun i j => raw22078 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw22078step0 raw22078; decide +kernel
      have hl : raw22078step0Labels = raw22078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22078 raw22078Labels permutation590 hz
    mixedMoment B raw22078step0 raw22078step0Labels = mixedMoment B raw22078step1 raw22078step1Labels := by
      have hz : ∀ j, raw22078step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22078step1 = (fun i j => raw22078step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22078step1 raw22078step0; decide +kernel
      have hl : raw22078step1Labels = raw22078step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22078step0 raw22078step0Labels permutation104 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw22079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22079 raw22079Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw22079 raw22079Labels = mixedMoment B raw22079step0 raw22079step0Labels := by
      have hz : ∀ j, raw22079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22079step0 = (fun i j => raw22079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22079step0 raw22079; decide +kernel
      have hl : raw22079step0Labels = raw22079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22079 raw22079Labels permutation434 hz
    _ = mixedMoment B node787 node787Labels := by rfl

def raw22080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22080 raw22080Labels = mixedMoment B node1639 node1639Labels := by
  calc
    mixedMoment B raw22080 raw22080Labels = mixedMoment B raw22080step0 raw22080step0Labels := by
      have hz : ∀ j, raw22080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22080step0 = (fun i j => raw22080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22080step0 raw22080; decide +kernel
      have hl : raw22080step0Labels = raw22080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22080 raw22080Labels permutation434 hz
    _ = mixedMoment B node1639 node1639Labels := by rfl

def raw22081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22081 raw22081Labels = mixedMoment B node1639 node1639Labels := by
  calc
    mixedMoment B raw22081 raw22081Labels = mixedMoment B raw22081step0 raw22081step0Labels := by
      have hz : ∀ j, raw22081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22081step0 = (fun i j => raw22081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22081step0 raw22081; decide +kernel
      have hl : raw22081step0Labels = raw22081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22081 raw22081Labels permutation434 hz
    mixedMoment B raw22081step0 raw22081step0Labels = mixedMoment B raw22081step1 raw22081step1Labels := by
      have ha : raw22081step1 = (fun i j => raw22081step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22081step1 raw22081step0; decide +kernel
      have hl : raw22081step1Labels = raw22081step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22081step0 raw22081step0Labels permutation38 permutation2
    _ = mixedMoment B node1639 node1639Labels := by rfl

def raw22082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22082 raw22082Labels = mixedMoment B node1593 node1593Labels := by
  calc
    mixedMoment B raw22082 raw22082Labels = mixedMoment B raw22082step0 raw22082step0Labels := by
      have ha : raw22082step0 = (fun i j => raw22082 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22082step0 raw22082; decide +kernel
      have hl : raw22082step0Labels = raw22082Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22082 raw22082Labels permutation200 permutation2
    _ = mixedMoment B node1593 node1593Labels := by rfl

def raw22083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw22083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22083 raw22083Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw22083 raw22083Labels = mixedMoment B raw22083step0 raw22083step0Labels := by
      have hz : ∀ j, raw22083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22083step0 = (fun i j => raw22083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22083step0 raw22083; decide +kernel
      have hl : raw22083step0Labels = raw22083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22083 raw22083Labels permutation434 hz
    _ = mixedMoment B node1700 node1700Labels := by rfl

def raw22084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22084 raw22084Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw22084 raw22084Labels = mixedMoment B raw22084step0 raw22084step0Labels := by
      have hz : ∀ j, raw22084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22084step0 = (fun i j => raw22084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22084step0 raw22084; decide +kernel
      have hl : raw22084step0Labels = raw22084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22084 raw22084Labels permutation434 hz
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw22085 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw22085Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22085step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw22085step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22085 raw22085Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw22085 raw22085Labels = mixedMoment B raw22085step0 raw22085step0Labels := by
      have hz : ∀ j, raw22085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22085step0 = (fun i j => raw22085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22085step0 raw22085; decide +kernel
      have hl : raw22085step0Labels = raw22085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22085 raw22085Labels permutation434 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw22086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22086 raw22086Labels = mixedMoment B node542 node542Labels := by
  calc
    mixedMoment B raw22086 raw22086Labels = mixedMoment B raw22086step0 raw22086step0Labels := by
      have hz : ∀ j, raw22086 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22086step0 = (fun i j => raw22086 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22086step0 raw22086; decide +kernel
      have hl : raw22086step0Labels = raw22086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22086 raw22086Labels permutation434 hz
    mixedMoment B raw22086step0 raw22086step0Labels = mixedMoment B raw22086step1 raw22086step1Labels := by
      have ha : raw22086step1 = (fun i j => raw22086step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22086step1 raw22086step0; decide +kernel
      have hl : raw22086step1Labels = raw22086step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22086step0 raw22086step0Labels permutation38 permutation2
    _ = mixedMoment B node542 node542Labels := by rfl

def raw22087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22087 raw22087Labels = mixedMoment B node737 node737Labels := by
  calc
    mixedMoment B raw22087 raw22087Labels = mixedMoment B raw22087step0 raw22087step0Labels := by
      have hz : ∀ j, raw22087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22087step0 = (fun i j => raw22087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22087step0 raw22087; decide +kernel
      have hl : raw22087step0Labels = raw22087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22087 raw22087Labels permutation434 hz
    mixedMoment B raw22087step0 raw22087step0Labels = mixedMoment B raw22087step1 raw22087step1Labels := by
      have ha : raw22087step1 = (fun i j => raw22087step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22087step1 raw22087step0; decide +kernel
      have hl : raw22087step1Labels = raw22087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22087step0 raw22087step0Labels permutation38 permutation2
    _ = mixedMoment B node737 node737Labels := by rfl

def raw22088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw22088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22088 raw22088Labels = mixedMoment B node702 node702Labels := by
  calc
    mixedMoment B raw22088 raw22088Labels = mixedMoment B raw22088step0 raw22088step0Labels := by
      have ha : raw22088step0 = (fun i j => raw22088 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22088step0 raw22088; decide +kernel
      have hl : raw22088step0Labels = raw22088Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22088 raw22088Labels permutation206 permutation2
    _ = mixedMoment B node702 node702Labels := by rfl

def raw22089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw22089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw22089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw22089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22089 raw22089Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw22089 raw22089Labels = mixedMoment B raw22089step0 raw22089step0Labels := by
      have hz : ∀ j, raw22089 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22089step0 = (fun i j => raw22089 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22089step0 raw22089; decide +kernel
      have hl : raw22089step0Labels = raw22089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22089 raw22089Labels permutation434 hz
    mixedMoment B raw22089step0 raw22089step0Labels = mixedMoment B raw22089step1 raw22089step1Labels := by
      have ha : raw22089step1 = (fun i j => raw22089step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22089step1 raw22089step0; decide +kernel
      have hl : raw22089step1Labels = raw22089step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22089step0 raw22089step0Labels permutation40 permutation2
    _ = mixedMoment B node787 node787Labels := by rfl

def raw22090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22090 raw22090Labels = mixedMoment B node810 node810Labels := by
  calc
    mixedMoment B raw22090 raw22090Labels = mixedMoment B raw22090step0 raw22090step0Labels := by
      have hz : ∀ j, raw22090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22090step0 = (fun i j => raw22090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22090step0 raw22090; decide +kernel
      have hl : raw22090step0Labels = raw22090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22090 raw22090Labels permutation434 hz
    mixedMoment B raw22090step0 raw22090step0Labels = mixedMoment B raw22090step1 raw22090step1Labels := by
      have ha : raw22090step1 = (fun i j => raw22090step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22090step1 raw22090step0; decide +kernel
      have hl : raw22090step1Labels = raw22090step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22090step0 raw22090step0Labels permutation38 permutation2
    _ = mixedMoment B node810 node810Labels := by rfl

def raw22091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22091 raw22091Labels = mixedMoment B node810 node810Labels := by
  calc
    mixedMoment B raw22091 raw22091Labels = mixedMoment B raw22091step0 raw22091step0Labels := by
      have hz : ∀ j, raw22091 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22091step0 = (fun i j => raw22091 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22091step0 raw22091; decide +kernel
      have hl : raw22091step0Labels = raw22091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22091 raw22091Labels permutation434 hz
    _ = mixedMoment B node810 node810Labels := by rfl

def raw22092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22092 raw22092Labels = mixedMoment B node783 node783Labels := by
  calc
    _ = mixedMoment B node783 node783Labels := by rfl

def raw22093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22093 raw22093Labels = mixedMoment B node790 node790Labels := by
  calc
    mixedMoment B raw22093 raw22093Labels = mixedMoment B raw22093step0 raw22093step0Labels := by
      have hz : ∀ j, raw22093 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22093step0 = (fun i j => raw22093 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22093step0 raw22093; decide +kernel
      have hl : raw22093step0Labels = raw22093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22093 raw22093Labels permutation434 hz
    _ = mixedMoment B node790 node790Labels := by rfl

def raw22094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22094 raw22094Labels = mixedMoment B node551 node551Labels := by
  calc
    mixedMoment B raw22094 raw22094Labels = mixedMoment B raw22094step0 raw22094step0Labels := by
      have hz : ∀ j, raw22094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22094step0 = (fun i j => raw22094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22094step0 raw22094; decide +kernel
      have hl : raw22094step0Labels = raw22094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22094 raw22094Labels permutation434 hz
    mixedMoment B raw22094step0 raw22094step0Labels = mixedMoment B raw22094step1 raw22094step1Labels := by
      have ha : raw22094step1 = (fun i j => raw22094step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22094step1 raw22094step0; decide +kernel
      have hl : raw22094step1Labels = raw22094step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22094step0 raw22094step0Labels permutation32 permutation4
    mixedMoment B raw22094step1 raw22094step1Labels = mixedMoment B raw22094step2 raw22094step2Labels := by
      have ha : raw22094step2 = -raw22094step1 := by apply Matrix.ext; change ∀ i j, raw22094step2 i j = -(raw22094step1 i j); unfold raw22094step2 raw22094step1; decide +kernel
      have hl : raw22094step2Labels = raw22094step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node551 node551Labels := by rfl

def raw22095 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw22095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22095step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22095step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22095step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22095 raw22095Labels = mixedMoment B node851 node851Labels := by
  calc
    mixedMoment B raw22095 raw22095Labels = mixedMoment B raw22095step0 raw22095step0Labels := by
      have hz : ∀ j, raw22095 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22095step0 = (fun i j => raw22095 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22095step0 raw22095; decide +kernel
      have hl : raw22095step0Labels = raw22095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22095 raw22095Labels permutation434 hz
    mixedMoment B raw22095step0 raw22095step0Labels = mixedMoment B raw22095step1 raw22095step1Labels := by
      have hz : ∀ j, raw22095step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22095step1 = (fun i j => raw22095step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22095step1 raw22095step0; decide +kernel
      have hl : raw22095step1Labels = raw22095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22095step0 raw22095step0Labels permutation56 hz
    mixedMoment B raw22095step1 raw22095step1Labels = mixedMoment B raw22095step2 raw22095step2Labels := by
      have ha : raw22095step2 = (fun i j => raw22095step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22095step2 raw22095step1; decide +kernel
      have hl : raw22095step2Labels = raw22095step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22095step1 raw22095step1Labels permutation8 permutation4
    mixedMoment B raw22095step2 raw22095step2Labels = mixedMoment B raw22095step3 raw22095step3Labels := by
      have ha : raw22095step3 = -raw22095step2 := by apply Matrix.ext; change ∀ i j, raw22095step3 i j = -(raw22095step2 i j); unfold raw22095step3 raw22095step2; decide +kernel
      have hl : raw22095step3Labels = raw22095step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node851 node851Labels := by rfl

def raw22096 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw22096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22096 raw22096Labels = mixedMoment B node804 node804Labels := by
  calc
    mixedMoment B raw22096 raw22096Labels = mixedMoment B raw22096step0 raw22096step0Labels := by
      have hz : ∀ j, raw22096 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22096step0 = (fun i j => raw22096 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22096step0 raw22096; decide +kernel
      have hl : raw22096step0Labels = raw22096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22096 raw22096Labels permutation434 hz
    mixedMoment B raw22096step0 raw22096step0Labels = mixedMoment B raw22096step1 raw22096step1Labels := by
      have ha : raw22096step1 = (fun i j => raw22096step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22096step1 raw22096step0; decide +kernel
      have hl : raw22096step1Labels = raw22096step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22096step0 raw22096step0Labels permutation44 permutation4
    mixedMoment B raw22096step1 raw22096step1Labels = mixedMoment B raw22096step2 raw22096step2Labels := by
      have ha : raw22096step2 = -raw22096step1 := by apply Matrix.ext; change ∀ i j, raw22096step2 i j = -(raw22096step1 i j); unfold raw22096step2 raw22096step1; decide +kernel
      have hl : raw22096step2Labels = raw22096step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node804 node804Labels := by rfl

def raw22097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22097 raw22097Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw22097 raw22097Labels = mixedMoment B raw22097step0 raw22097step0Labels := by
      have hz : ∀ j, raw22097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22097step0 = (fun i j => raw22097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22097step0 raw22097; decide +kernel
      have hl : raw22097step0Labels = raw22097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22097 raw22097Labels permutation434 hz
    _ = mixedMoment B node785 node785Labels := by rfl

def raw22098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22098 raw22098Labels = mixedMoment B node1637 node1637Labels := by
  calc
    mixedMoment B raw22098 raw22098Labels = mixedMoment B raw22098step0 raw22098step0Labels := by
      have hz : ∀ j, raw22098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22098step0 = (fun i j => raw22098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22098step0 raw22098; decide +kernel
      have hl : raw22098step0Labels = raw22098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22098 raw22098Labels permutation434 hz
    _ = mixedMoment B node1637 node1637Labels := by rfl

def raw22099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22099 raw22099Labels = mixedMoment B node1637 node1637Labels := by
  calc
    mixedMoment B raw22099 raw22099Labels = mixedMoment B raw22099step0 raw22099step0Labels := by
      have hz : ∀ j, raw22099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22099step0 = (fun i j => raw22099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22099step0 raw22099; decide +kernel
      have hl : raw22099step0Labels = raw22099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22099 raw22099Labels permutation434 hz
    mixedMoment B raw22099step0 raw22099step0Labels = mixedMoment B raw22099step1 raw22099step1Labels := by
      have ha : raw22099step1 = (fun i j => raw22099step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22099step1 raw22099step0; decide +kernel
      have hl : raw22099step1Labels = raw22099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22099step0 raw22099step0Labels permutation38 permutation2
    _ = mixedMoment B node1637 node1637Labels := by rfl

def raw22100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22100 raw22100Labels = mixedMoment B node1592 node1592Labels := by
  calc
    mixedMoment B raw22100 raw22100Labels = mixedMoment B raw22100step0 raw22100step0Labels := by
      have ha : raw22100step0 = (fun i j => raw22100 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22100step0 raw22100; decide +kernel
      have hl : raw22100step0Labels = raw22100Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22100 raw22100Labels permutation200 permutation2
    _ = mixedMoment B node1592 node1592Labels := by rfl

def raw22101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw22101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22101 raw22101Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw22101 raw22101Labels = mixedMoment B raw22101step0 raw22101step0Labels := by
      have hz : ∀ j, raw22101 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22101step0 = (fun i j => raw22101 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22101step0 raw22101; decide +kernel
      have hl : raw22101step0Labels = raw22101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22101 raw22101Labels permutation520 hz
    mixedMoment B raw22101step0 raw22101step0Labels = mixedMoment B raw22101step1 raw22101step1Labels := by
      have hz : ∀ j, raw22101step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22101step1 = (fun i j => raw22101step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22101step1 raw22101step0; decide +kernel
      have hl : raw22101step1Labels = raw22101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22101step0 raw22101step0Labels permutation104 hz
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw22102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22102 raw22102Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw22102 raw22102Labels = mixedMoment B raw22102step0 raw22102step0Labels := by
      have hz : ∀ j, raw22102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22102step0 = (fun i j => raw22102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22102step0 raw22102; decide +kernel
      have hl : raw22102step0Labels = raw22102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22102 raw22102Labels permutation434 hz
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw22103 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]
def raw22103Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22103step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]
def raw22103step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22103step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22103step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22103 raw22103Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22103 raw22103Labels = mixedMoment B raw22103step0 raw22103step0Labels := by
      have hz : ∀ j, raw22103 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22103step0 = (fun i j => raw22103 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22103step0 raw22103; decide +kernel
      have hl : raw22103step0Labels = raw22103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22103 raw22103Labels permutation520 hz
    mixedMoment B raw22103step0 raw22103step0Labels = mixedMoment B raw22103step1 raw22103step1Labels := by
      have hz : ∀ j, raw22103step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22103step1 = (fun i j => raw22103step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22103step1 raw22103step0; decide +kernel
      have hl : raw22103step1Labels = raw22103step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22103step0 raw22103step0Labels permutation104 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw22104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22104 raw22104Labels = mixedMoment B node538 node538Labels := by
  calc
    mixedMoment B raw22104 raw22104Labels = mixedMoment B raw22104step0 raw22104step0Labels := by
      have hz : ∀ j, raw22104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22104step0 = (fun i j => raw22104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22104step0 raw22104; decide +kernel
      have hl : raw22104step0Labels = raw22104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22104 raw22104Labels permutation434 hz
    mixedMoment B raw22104step0 raw22104step0Labels = mixedMoment B raw22104step1 raw22104step1Labels := by
      have ha : raw22104step1 = (fun i j => raw22104step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22104step1 raw22104step0; decide +kernel
      have hl : raw22104step1Labels = raw22104step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22104step0 raw22104step0Labels permutation40 permutation2
    _ = mixedMoment B node538 node538Labels := by rfl

def raw22105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw22105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22105 raw22105Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw22105 raw22105Labels = mixedMoment B raw22105step0 raw22105step0Labels := by
      have hz : ∀ j, raw22105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22105step0 = (fun i j => raw22105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22105step0 raw22105; decide +kernel
      have hl : raw22105step0Labels = raw22105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22105 raw22105Labels permutation434 hz
    mixedMoment B raw22105step0 raw22105step0Labels = mixedMoment B raw22105step1 raw22105step1Labels := by
      have ha : raw22105step1 = (fun i j => raw22105step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22105step1 raw22105step0; decide +kernel
      have hl : raw22105step1Labels = raw22105step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22105step0 raw22105step0Labels permutation40 permutation2
    _ = mixedMoment B node733 node733Labels := by rfl

def raw22106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw22106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22106 raw22106Labels = mixedMoment B node699 node699Labels := by
  calc
    mixedMoment B raw22106 raw22106Labels = mixedMoment B raw22106step0 raw22106step0Labels := by
      have ha : raw22106step0 = (fun i j => raw22106 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22106step0 raw22106; decide +kernel
      have hl : raw22106step0Labels = raw22106Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22106 raw22106Labels permutation208 permutation2
    _ = mixedMoment B node699 node699Labels := by rfl

def raw22107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw22107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw22107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22107step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22107 raw22107Labels = mixedMoment B node812 node812Labels := by
  calc
    mixedMoment B raw22107 raw22107Labels = mixedMoment B raw22107step0 raw22107step0Labels := by
      have hz : ∀ j, raw22107 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22107step0 = (fun i j => raw22107 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22107step0 raw22107; decide +kernel
      have hl : raw22107step0Labels = raw22107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22107 raw22107Labels permutation520 hz
    mixedMoment B raw22107step0 raw22107step0Labels = mixedMoment B raw22107step1 raw22107step1Labels := by
      have hz : ∀ j, raw22107step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22107step1 = (fun i j => raw22107step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22107step1 raw22107step0; decide +kernel
      have hl : raw22107step1Labels = raw22107step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22107step0 raw22107step0Labels permutation104 hz
    mixedMoment B raw22107step1 raw22107step1Labels = mixedMoment B raw22107step2 raw22107step2Labels := by
      have ha : raw22107step2 = (fun i j => raw22107step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22107step2 raw22107step1; decide +kernel
      have hl : raw22107step2Labels = raw22107step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22107step1 raw22107step1Labels permutation10 permutation2
    _ = mixedMoment B node812 node812Labels := by rfl

def raw22108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22108 raw22108Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw22108 raw22108Labels = mixedMoment B raw22108step0 raw22108step0Labels := by
      have hz : ∀ j, raw22108 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22108step0 = (fun i j => raw22108 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22108step0 raw22108; decide +kernel
      have hl : raw22108step0Labels = raw22108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22108 raw22108Labels permutation434 hz
    mixedMoment B raw22108step0 raw22108step0Labels = mixedMoment B raw22108step1 raw22108step1Labels := by
      have ha : raw22108step1 = (fun i j => raw22108step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22108step1 raw22108step0; decide +kernel
      have hl : raw22108step1Labels = raw22108step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22108step0 raw22108step0Labels permutation40 permutation2
    _ = mixedMoment B node806 node806Labels := by rfl

def raw22109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw22109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22109 raw22109Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw22109 raw22109Labels = mixedMoment B raw22109step0 raw22109step0Labels := by
      have hz : ∀ j, raw22109 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22109step0 = (fun i j => raw22109 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22109step0 raw22109; decide +kernel
      have hl : raw22109step0Labels = raw22109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22109 raw22109Labels permutation434 hz
    mixedMoment B raw22109step0 raw22109step0Labels = mixedMoment B raw22109step1 raw22109step1Labels := by
      have ha : raw22109step1 = (fun i j => raw22109step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22109step1 raw22109step0; decide +kernel
      have hl : raw22109step1Labels = raw22109step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22109step0 raw22109step0Labels permutation34 permutation2
    _ = mixedMoment B node806 node806Labels := by rfl

def raw22110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22110 raw22110Labels = mixedMoment B node782 node782Labels := by
  calc
    _ = mixedMoment B node782 node782Labels := by rfl

def raw22111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22111 raw22111Labels = mixedMoment B node789 node789Labels := by
  calc
    mixedMoment B raw22111 raw22111Labels = mixedMoment B raw22111step0 raw22111step0Labels := by
      have hz : ∀ j, raw22111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22111step0 = (fun i j => raw22111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22111step0 raw22111; decide +kernel
      have hl : raw22111step0Labels = raw22111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22111 raw22111Labels permutation434 hz
    _ = mixedMoment B node789 node789Labels := by rfl

def raw22112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw22112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw22112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22112 raw22112Labels = mixedMoment B node536 node536Labels := by
  calc
    mixedMoment B raw22112 raw22112Labels = mixedMoment B raw22112step0 raw22112step0Labels := by
      have hz : ∀ j, raw22112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22112step0 = (fun i j => raw22112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22112step0 raw22112; decide +kernel
      have hl : raw22112step0Labels = raw22112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22112 raw22112Labels permutation434 hz
    mixedMoment B raw22112step0 raw22112step0Labels = mixedMoment B raw22112step1 raw22112step1Labels := by
      have ha : raw22112step1 = (fun i j => raw22112step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22112step1 raw22112step0; decide +kernel
      have hl : raw22112step1Labels = raw22112step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22112step0 raw22112step0Labels permutation44 permutation4
    mixedMoment B raw22112step1 raw22112step1Labels = mixedMoment B raw22112step2 raw22112step2Labels := by
      have ha : raw22112step2 = -raw22112step1 := by apply Matrix.ext; change ∀ i j, raw22112step2 i j = -(raw22112step1 i j); unfold raw22112step2 raw22112step1; decide +kernel
      have hl : raw22112step2Labels = raw22112step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node536 node536Labels := by rfl

def raw22113 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw22113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw22113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22113step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw22113step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22113 raw22113Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw22113 raw22113Labels = mixedMoment B raw22113step0 raw22113step0Labels := by
      have hz : ∀ j, raw22113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22113step0 = (fun i j => raw22113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22113step0 raw22113; decide +kernel
      have hl : raw22113step0Labels = raw22113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22113 raw22113Labels permutation434 hz
    mixedMoment B raw22113step0 raw22113step0Labels = mixedMoment B raw22113step1 raw22113step1Labels := by
      have hz : ∀ j, raw22113step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22113step1 = (fun i j => raw22113step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22113step1 raw22113step0; decide +kernel
      have hl : raw22113step1Labels = raw22113step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22113step0 raw22113step0Labels permutation56 hz
    mixedMoment B raw22113step1 raw22113step1Labels = mixedMoment B raw22113step2 raw22113step2Labels := by
      have ha : raw22113step2 = (fun i j => raw22113step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22113step2 raw22113step1; decide +kernel
      have hl : raw22113step2Labels = raw22113step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22113step1 raw22113step1Labels permutation10 permutation4
    mixedMoment B raw22113step2 raw22113step2Labels = mixedMoment B raw22113step3 raw22113step3Labels := by
      have ha : raw22113step3 = -raw22113step2 := by apply Matrix.ext; change ∀ i j, raw22113step3 i j = -(raw22113step2 i j); unfold raw22113step3 raw22113step2; decide +kernel
      have hl : raw22113step3Labels = raw22113step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node809 node809Labels := by rfl

def raw22114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22114 raw22114Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw22114 raw22114Labels = mixedMoment B raw22114step0 raw22114step0Labels := by
      have hz : ∀ j, raw22114 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22114step0 = (fun i j => raw22114 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22114step0 raw22114; decide +kernel
      have hl : raw22114step0Labels = raw22114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22114 raw22114Labels permutation434 hz
    mixedMoment B raw22114step0 raw22114step0Labels = mixedMoment B raw22114step1 raw22114step1Labels := by
      have hz : ∀ j, raw22114step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22114step1 = (fun i j => raw22114step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22114step1 raw22114step0; decide +kernel
      have hl : raw22114step1Labels = raw22114step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22114step0 raw22114step0Labels permutation80 hz
    _ = mixedMoment B node813 node813Labels := by rfl

def raw22115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22115 raw22115Labels = mixedMoment B node1651 node1651Labels := by
  calc
    mixedMoment B raw22115 raw22115Labels = mixedMoment B raw22115step0 raw22115step0Labels := by
      have hz : ∀ j, raw22115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22115step0 = (fun i j => raw22115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22115step0 raw22115; decide +kernel
      have hl : raw22115step0Labels = raw22115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22115 raw22115Labels permutation434 hz
    mixedMoment B raw22115step0 raw22115step0Labels = mixedMoment B raw22115step1 raw22115step1Labels := by
      have hz : ∀ j, raw22115step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22115step1 = (fun i j => raw22115step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22115step1 raw22115step0; decide +kernel
      have hl : raw22115step1Labels = raw22115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22115step0 raw22115step0Labels permutation80 hz
    _ = mixedMoment B node1651 node1651Labels := by rfl

def raw22116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22116 raw22116Labels = mixedMoment B node1603 node1603Labels := by
  calc
    mixedMoment B raw22116 raw22116Labels = mixedMoment B raw22116step0 raw22116step0Labels := by
      have hz : ∀ j, raw22116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22116step0 = (fun i j => raw22116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22116step0 raw22116; decide +kernel
      have hl : raw22116step0Labels = raw22116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22116 raw22116Labels permutation434 hz
    mixedMoment B raw22116step0 raw22116step0Labels = mixedMoment B raw22116step1 raw22116step1Labels := by
      have ha : raw22116step1 = (fun i j => raw22116step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22116step1 raw22116step0; decide +kernel
      have hl : raw22116step1Labels = raw22116step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22116step0 raw22116step0Labels permutation38 permutation2
    _ = mixedMoment B node1603 node1603Labels := by rfl

def raw22117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw22117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw22117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22117 raw22117Labels = mixedMoment B node1603 node1603Labels := by
  calc
    mixedMoment B raw22117 raw22117Labels = mixedMoment B raw22117step0 raw22117step0Labels := by
      have hz : ∀ j, raw22117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22117step0 = (fun i j => raw22117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22117step0 raw22117; decide +kernel
      have hl : raw22117step0Labels = raw22117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22117 raw22117Labels permutation346 hz
    mixedMoment B raw22117step0 raw22117step0Labels = mixedMoment B raw22117step1 raw22117step1Labels := by
      have ha : raw22117step1 = (fun i j => raw22117step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22117step1 raw22117step0; decide +kernel
      have hl : raw22117step1Labels = raw22117step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22117step0 raw22117step0Labels permutation38 permutation2
    _ = mixedMoment B node1603 node1603Labels := by rfl

def raw22118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw22118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw22118step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw22118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22118 raw22118Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw22118 raw22118Labels = mixedMoment B raw22118step0 raw22118step0Labels := by
      have hz : ∀ j, raw22118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22118step0 = (fun i j => raw22118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22118step0 raw22118; decide +kernel
      have hl : raw22118step0Labels = raw22118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22118 raw22118Labels permutation434 hz
    mixedMoment B raw22118step0 raw22118step0Labels = mixedMoment B raw22118step1 raw22118step1Labels := by
      have hz : ∀ j, raw22118step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22118step1 = (fun i j => raw22118step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22118step1 raw22118step0; decide +kernel
      have hl : raw22118step1Labels = raw22118step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22118step0 raw22118step0Labels permutation80 hz
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw22119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22119 raw22119Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw22119 raw22119Labels = mixedMoment B raw22119step0 raw22119step0Labels := by
      have hz : ∀ j, raw22119 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22119step0 = (fun i j => raw22119 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22119step0 raw22119; decide +kernel
      have hl : raw22119step0Labels = raw22119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22119 raw22119Labels permutation434 hz
    mixedMoment B raw22119step0 raw22119step0Labels = mixedMoment B raw22119step1 raw22119step1Labels := by
      have hz : ∀ j, raw22119step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22119step1 = (fun i j => raw22119step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22119step1 raw22119step0; decide +kernel
      have hl : raw22119step1Labels = raw22119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22119step0 raw22119step0Labels permutation80 hz
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw22120 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw22120Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22120step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![2, -2], ![1, -1]]
def raw22120step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22120step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw22120step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22120step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22120step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22120 raw22120Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22120 raw22120Labels = mixedMoment B raw22120step0 raw22120step0Labels := by
      have hz : ∀ j, raw22120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22120step0 = (fun i j => raw22120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22120step0 raw22120; decide +kernel
      have hl : raw22120step0Labels = raw22120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22120 raw22120Labels permutation434 hz
    mixedMoment B raw22120step0 raw22120step0Labels = mixedMoment B raw22120step1 raw22120step1Labels := by
      have hz : ∀ j, raw22120step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22120step1 = (fun i j => raw22120step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22120step1 raw22120step0; decide +kernel
      have hl : raw22120step1Labels = raw22120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22120step0 raw22120step0Labels permutation80 hz
    mixedMoment B raw22120step1 raw22120step1Labels = mixedMoment B raw22120step2 raw22120step2Labels := by
      have ha : raw22120step2 = (fun i j => raw22120step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22120step2 raw22120step1; decide +kernel
      have hl : raw22120step2Labels = raw22120step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22120step1 raw22120step1Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw22121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw22121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22121 raw22121Labels = mixedMoment B node548 node548Labels := by
  calc
    mixedMoment B raw22121 raw22121Labels = mixedMoment B raw22121step0 raw22121step0Labels := by
      have hz : ∀ j, raw22121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22121step0 = (fun i j => raw22121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22121step0 raw22121; decide +kernel
      have hl : raw22121step0Labels = raw22121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22121 raw22121Labels permutation434 hz
    mixedMoment B raw22121step0 raw22121step0Labels = mixedMoment B raw22121step1 raw22121step1Labels := by
      have hz : ∀ j, raw22121step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22121step1 = (fun i j => raw22121step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22121step1 raw22121step0; decide +kernel
      have hl : raw22121step1Labels = raw22121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22121step0 raw22121step0Labels permutation80 hz
    _ = mixedMoment B node548 node548Labels := by rfl

def raw22122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw22122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22122 raw22122Labels = mixedMoment B node743 node743Labels := by
  calc
    mixedMoment B raw22122 raw22122Labels = mixedMoment B raw22122step0 raw22122step0Labels := by
      have hz : ∀ j, raw22122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22122step0 = (fun i j => raw22122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22122step0 raw22122; decide +kernel
      have hl : raw22122step0Labels = raw22122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22122 raw22122Labels permutation434 hz
    mixedMoment B raw22122step0 raw22122step0Labels = mixedMoment B raw22122step1 raw22122step1Labels := by
      have hz : ∀ j, raw22122step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22122step1 = (fun i j => raw22122step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22122step1 raw22122step0; decide +kernel
      have hl : raw22122step1Labels = raw22122step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22122step0 raw22122step0Labels permutation80 hz
    _ = mixedMoment B node743 node743Labels := by rfl

def raw22123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw22123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22123 raw22123Labels = mixedMoment B node708 node708Labels := by
  calc
    mixedMoment B raw22123 raw22123Labels = mixedMoment B raw22123step0 raw22123step0Labels := by
      have hz : ∀ j, raw22123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22123step0 = (fun i j => raw22123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22123step0 raw22123; decide +kernel
      have hl : raw22123step0Labels = raw22123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22123 raw22123Labels permutation434 hz
    mixedMoment B raw22123step0 raw22123step0Labels = mixedMoment B raw22123step1 raw22123step1Labels := by
      have ha : raw22123step1 = (fun i j => raw22123step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22123step1 raw22123step0; decide +kernel
      have hl : raw22123step1Labels = raw22123step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22123step0 raw22123step0Labels permutation38 permutation2
    _ = mixedMoment B node708 node708Labels := by rfl

def raw22124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw22124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw22124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22124 raw22124Labels = mixedMoment B node708 node708Labels := by
  calc
    mixedMoment B raw22124 raw22124Labels = mixedMoment B raw22124step0 raw22124step0Labels := by
      have hz : ∀ j, raw22124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22124step0 = (fun i j => raw22124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22124step0 raw22124; decide +kernel
      have hl : raw22124step0Labels = raw22124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22124 raw22124Labels permutation346 hz
    mixedMoment B raw22124step0 raw22124step0Labels = mixedMoment B raw22124step1 raw22124step1Labels := by
      have ha : raw22124step1 = (fun i j => raw22124step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22124step1 raw22124step0; decide +kernel
      have hl : raw22124step1Labels = raw22124step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22124step0 raw22124step0Labels permutation38 permutation2
    _ = mixedMoment B node708 node708Labels := by rfl

def raw22125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw22125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw22125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, 0, -2], ![2, -1, -1]]
def raw22125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22125 raw22125Labels = mixedMoment B node816 node816Labels := by
  calc
    mixedMoment B raw22125 raw22125Labels = mixedMoment B raw22125step0 raw22125step0Labels := by
      have hz : ∀ j, raw22125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22125step0 = (fun i j => raw22125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22125step0 raw22125; decide +kernel
      have hl : raw22125step0Labels = raw22125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22125 raw22125Labels permutation434 hz
    mixedMoment B raw22125step0 raw22125step0Labels = mixedMoment B raw22125step1 raw22125step1Labels := by
      have hz : ∀ j, raw22125step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22125step1 = (fun i j => raw22125step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22125step1 raw22125step0; decide +kernel
      have hl : raw22125step1Labels = raw22125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22125step0 raw22125step0Labels permutation80 hz
    mixedMoment B raw22125step1 raw22125step1Labels = mixedMoment B raw22125step2 raw22125step2Labels := by
      have ha : raw22125step2 = (fun i j => raw22125step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22125step2 raw22125step1; decide +kernel
      have hl : raw22125step2Labels = raw22125step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22125step1 raw22125step1Labels permutation9 permutation2
    _ = mixedMoment B node816 node816Labels := by rfl

def raw22126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22126 raw22126Labels = mixedMoment B node856 node856Labels := by
  calc
    mixedMoment B raw22126 raw22126Labels = mixedMoment B raw22126step0 raw22126step0Labels := by
      have hz : ∀ j, raw22126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22126step0 = (fun i j => raw22126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22126step0 raw22126; decide +kernel
      have hl : raw22126step0Labels = raw22126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22126 raw22126Labels permutation434 hz
    mixedMoment B raw22126step0 raw22126step0Labels = mixedMoment B raw22126step1 raw22126step1Labels := by
      have hz : ∀ j, raw22126step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22126step1 = (fun i j => raw22126step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22126step1 raw22126step0; decide +kernel
      have hl : raw22126step1Labels = raw22126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22126step0 raw22126step0Labels permutation80 hz
    _ = mixedMoment B node856 node856Labels := by rfl

def raw22127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22127 raw22127Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw22127 raw22127Labels = mixedMoment B raw22127step0 raw22127step0Labels := by
      have hz : ∀ j, raw22127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22127step0 = (fun i j => raw22127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22127step0 raw22127; decide +kernel
      have hl : raw22127step0Labels = raw22127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22127 raw22127Labels permutation434 hz
    _ = mixedMoment B node807 node807Labels := by rfl

def raw22128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22128 raw22128Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw22128 raw22128Labels = mixedMoment B raw22128step0 raw22128step0Labels := by
      have hz : ∀ j, raw22128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22128step0 = (fun i j => raw22128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22128step0 raw22128; decide +kernel
      have hl : raw22128step0Labels = raw22128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22128 raw22128Labels permutation346 hz
    _ = mixedMoment B node807 node807Labels := by rfl

def raw22129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22129step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22129step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22129 raw22129Labels = mixedMoment B node556 node556Labels := by
  calc
    mixedMoment B raw22129 raw22129Labels = mixedMoment B raw22129step0 raw22129step0Labels := by
      have hz : ∀ j, raw22129 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22129step0 = (fun i j => raw22129 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22129step0 raw22129; decide +kernel
      have hl : raw22129step0Labels = raw22129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22129 raw22129Labels permutation434 hz
    mixedMoment B raw22129step0 raw22129step0Labels = mixedMoment B raw22129step1 raw22129step1Labels := by
      have hz : ∀ j, raw22129step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22129step1 = (fun i j => raw22129step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22129step1 raw22129step0; decide +kernel
      have hl : raw22129step1Labels = raw22129step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22129step0 raw22129step0Labels permutation80 hz
    mixedMoment B raw22129step1 raw22129step1Labels = mixedMoment B raw22129step2 raw22129step2Labels := by
      have ha : raw22129step2 = (fun i j => raw22129step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22129step2 raw22129step1; decide +kernel
      have hl : raw22129step2Labels = raw22129step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22129step1 raw22129step1Labels permutation8 permutation4
    mixedMoment B raw22129step2 raw22129step2Labels = mixedMoment B raw22129step3 raw22129step3Labels := by
      have ha : raw22129step3 = -raw22129step2 := by apply Matrix.ext; change ∀ i j, raw22129step3 i j = -(raw22129step2 i j); unfold raw22129step3 raw22129step2; decide +kernel
      have hl : raw22129step3Labels = raw22129step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node556 node556Labels := by rfl

def raw22130 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22130step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22130 raw22130Labels = mixedMoment B node716 node716Labels := by
  calc
    mixedMoment B raw22130 raw22130Labels = mixedMoment B raw22130step0 raw22130step0Labels := by
      have hz : ∀ j, raw22130 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22130step0 = (fun i j => raw22130 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22130step0 raw22130; decide +kernel
      have hl : raw22130step0Labels = raw22130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22130 raw22130Labels permutation434 hz
    mixedMoment B raw22130step0 raw22130step0Labels = mixedMoment B raw22130step1 raw22130step1Labels := by
      have ha : raw22130step1 = (fun i j => raw22130step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22130step1 raw22130step0; decide +kernel
      have hl : raw22130step1Labels = raw22130step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22130step0 raw22130step0Labels permutation38 permutation4
    mixedMoment B raw22130step1 raw22130step1Labels = mixedMoment B raw22130step2 raw22130step2Labels := by
      have ha : raw22130step2 = -raw22130step1 := by apply Matrix.ext; change ∀ i j, raw22130step2 i j = -(raw22130step1 i j); unfold raw22130step2 raw22130step1; decide +kernel
      have hl : raw22130step2Labels = raw22130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node716 node716Labels := by rfl

def raw22131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw22131step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22131step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22131step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22131step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22131step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22131 raw22131Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw22131 raw22131Labels = mixedMoment B raw22131step0 raw22131step0Labels := by
      have hz : ∀ j, raw22131 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22131step0 = (fun i j => raw22131 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22131step0 raw22131; decide +kernel
      have hl : raw22131step0Labels = raw22131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22131 raw22131Labels permutation434 hz
    mixedMoment B raw22131step0 raw22131step0Labels = mixedMoment B raw22131step1 raw22131step1Labels := by
      have hz : ∀ j, raw22131step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22131step1 = (fun i j => raw22131step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22131step1 raw22131step0; decide +kernel
      have hl : raw22131step1Labels = raw22131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22131step0 raw22131step0Labels permutation80 hz
    mixedMoment B raw22131step1 raw22131step1Labels = mixedMoment B raw22131step2 raw22131step2Labels := by
      have ha : raw22131step2 = (fun i j => raw22131step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22131step2 raw22131step1; decide +kernel
      have hl : raw22131step2Labels = raw22131step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22131step1 raw22131step1Labels permutation8 permutation7
    mixedMoment B raw22131step2 raw22131step2Labels = mixedMoment B raw22131step3 raw22131step3Labels := by
      have ha : raw22131step3 = -raw22131step2 := by apply Matrix.ext; change ∀ i j, raw22131step3 i j = -(raw22131step2 i j); unfold raw22131step3 raw22131step2; decide +kernel
      have hl : raw22131step3Labels = raw22131step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22131step3 raw22131step3Labels = mixedMoment B raw22131step4 raw22131step4Labels := by
      have ha : raw22131step4 = raw22131step3 := by apply Matrix.ext; unfold raw22131step4 raw22131step3; decide +kernel
      have hl : raw22131step3Labels = labelEmbedding10 ∘ raw22131step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22131step3 raw22131step3Labels raw22131step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw22132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22132step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22132step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22132step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22132step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22132 raw22132Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw22132 raw22132Labels = mixedMoment B raw22132step0 raw22132step0Labels := by
      have hz : ∀ j, raw22132 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22132step0 = (fun i j => raw22132 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22132step0 raw22132; decide +kernel
      have hl : raw22132step0Labels = raw22132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22132 raw22132Labels permutation434 hz
    mixedMoment B raw22132step0 raw22132step0Labels = mixedMoment B raw22132step1 raw22132step1Labels := by
      have ha : raw22132step1 = (fun i j => raw22132step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22132step1 raw22132step0; decide +kernel
      have hl : raw22132step1Labels = raw22132step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22132step0 raw22132step0Labels permutation38 permutation7
    mixedMoment B raw22132step1 raw22132step1Labels = mixedMoment B raw22132step2 raw22132step2Labels := by
      have ha : raw22132step2 = -raw22132step1 := by apply Matrix.ext; change ∀ i j, raw22132step2 i j = -(raw22132step1 i j); unfold raw22132step2 raw22132step1; decide +kernel
      have hl : raw22132step2Labels = raw22132step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22132step2 raw22132step2Labels = mixedMoment B raw22132step3 raw22132step3Labels := by
      have ha : raw22132step3 = raw22132step2 := by apply Matrix.ext; unfold raw22132step3 raw22132step2; decide +kernel
      have hl : raw22132step2Labels = labelEmbedding10 ∘ raw22132step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22132step2 raw22132step2Labels raw22132step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw22133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw22133step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22133step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22133step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw22133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22133 raw22133Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw22133 raw22133Labels = mixedMoment B raw22133step0 raw22133step0Labels := by
      have hz : ∀ j, raw22133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22133step0 = (fun i j => raw22133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22133step0 raw22133; decide +kernel
      have hl : raw22133step0Labels = raw22133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22133 raw22133Labels permutation346 hz
    mixedMoment B raw22133step0 raw22133step0Labels = mixedMoment B raw22133step1 raw22133step1Labels := by
      have ha : raw22133step1 = (fun i j => raw22133step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22133step1 raw22133step0; decide +kernel
      have hl : raw22133step1Labels = raw22133step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22133step0 raw22133step0Labels permutation38 permutation7
    mixedMoment B raw22133step1 raw22133step1Labels = mixedMoment B raw22133step2 raw22133step2Labels := by
      have ha : raw22133step2 = -raw22133step1 := by apply Matrix.ext; change ∀ i j, raw22133step2 i j = -(raw22133step1 i j); unfold raw22133step2 raw22133step1; decide +kernel
      have hl : raw22133step2Labels = raw22133step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22133step2 raw22133step2Labels = mixedMoment B raw22133step3 raw22133step3Labels := by
      have ha : raw22133step3 = raw22133step2 := by apply Matrix.ext; unfold raw22133step3 raw22133step2; decide +kernel
      have hl : raw22133step2Labels = labelEmbedding10 ∘ raw22133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22133step2 raw22133step2Labels raw22133step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw22134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw22134step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22134step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22134step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22134step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw22134step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22134 raw22134Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw22134 raw22134Labels = mixedMoment B raw22134step0 raw22134step0Labels := by
      have hz : ∀ j, raw22134 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22134step0 = (fun i j => raw22134 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22134step0 raw22134; decide +kernel
      have hl : raw22134step0Labels = raw22134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22134 raw22134Labels permutation434 hz
    mixedMoment B raw22134step0 raw22134step0Labels = mixedMoment B raw22134step1 raw22134step1Labels := by
      have hz : ∀ j, raw22134step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22134step1 = (fun i j => raw22134step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22134step1 raw22134step0; decide +kernel
      have hl : raw22134step1Labels = raw22134step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22134step0 raw22134step0Labels permutation80 hz
    mixedMoment B raw22134step1 raw22134step1Labels = mixedMoment B raw22134step2 raw22134step2Labels := by
      have ha : raw22134step2 = (fun i j => raw22134step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22134step2 raw22134step1; decide +kernel
      have hl : raw22134step2Labels = raw22134step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22134step1 raw22134step1Labels permutation8 permutation7
    mixedMoment B raw22134step2 raw22134step2Labels = mixedMoment B raw22134step3 raw22134step3Labels := by
      have ha : raw22134step3 = -raw22134step2 := by apply Matrix.ext; change ∀ i j, raw22134step3 i j = -(raw22134step2 i j); unfold raw22134step3 raw22134step2; decide +kernel
      have hl : raw22134step3Labels = raw22134step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22134step3 raw22134step3Labels = mixedMoment B raw22134step4 raw22134step4Labels := by
      have ha : raw22134step4 = raw22134step3 := by apply Matrix.ext; unfold raw22134step4 raw22134step3; decide +kernel
      have hl : raw22134step3Labels = labelEmbedding10 ∘ raw22134step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22134step3 raw22134step3Labels raw22134step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw22135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22135step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw22135step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22135step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22135step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22135step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22135step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22135 raw22135Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw22135 raw22135Labels = mixedMoment B raw22135step0 raw22135step0Labels := by
      have hz : ∀ j, raw22135 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22135step0 = (fun i j => raw22135 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22135step0 raw22135; decide +kernel
      have hl : raw22135step0Labels = raw22135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22135 raw22135Labels permutation434 hz
    mixedMoment B raw22135step0 raw22135step0Labels = mixedMoment B raw22135step1 raw22135step1Labels := by
      have hz : ∀ j, raw22135step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22135step1 = (fun i j => raw22135step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22135step1 raw22135step0; decide +kernel
      have hl : raw22135step1Labels = raw22135step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22135step0 raw22135step0Labels permutation80 hz
    mixedMoment B raw22135step1 raw22135step1Labels = mixedMoment B raw22135step2 raw22135step2Labels := by
      have ha : raw22135step2 = (fun i j => raw22135step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22135step2 raw22135step1; decide +kernel
      have hl : raw22135step2Labels = raw22135step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22135step1 raw22135step1Labels permutation8 permutation7
    mixedMoment B raw22135step2 raw22135step2Labels = mixedMoment B raw22135step3 raw22135step3Labels := by
      have ha : raw22135step3 = -raw22135step2 := by apply Matrix.ext; change ∀ i j, raw22135step3 i j = -(raw22135step2 i j); unfold raw22135step3 raw22135step2; decide +kernel
      have hl : raw22135step3Labels = raw22135step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22135step3 raw22135step3Labels = mixedMoment B raw22135step4 raw22135step4Labels := by
      have ha : raw22135step4 = raw22135step3 := by apply Matrix.ext; unfold raw22135step4 raw22135step3; decide +kernel
      have hl : raw22135step3Labels = labelEmbedding10 ∘ raw22135step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22135step3 raw22135step3Labels raw22135step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw22136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22136 raw22136Labels = mixedMoment B node4127 node4127Labels := by
  calc
    mixedMoment B raw22136 raw22136Labels = mixedMoment B raw22136step0 raw22136step0Labels := by
      have hz : ∀ j, raw22136 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22136step0 = (fun i j => raw22136 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22136step0 raw22136; decide +kernel
      have hl : raw22136step0Labels = raw22136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22136 raw22136Labels permutation434 hz
    mixedMoment B raw22136step0 raw22136step0Labels = mixedMoment B raw22136step1 raw22136step1Labels := by
      have hz : ∀ j, raw22136step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22136step1 = (fun i j => raw22136step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22136step1 raw22136step0; decide +kernel
      have hl : raw22136step1Labels = raw22136step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22136step0 raw22136step0Labels permutation80 hz
    _ = mixedMoment B node4127 node4127Labels := by rfl

def raw22137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22137 raw22137Labels = mixedMoment B node4218 node4218Labels := by
  calc
    mixedMoment B raw22137 raw22137Labels = mixedMoment B raw22137step0 raw22137step0Labels := by
      have hz : ∀ j, raw22137 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22137step0 = (fun i j => raw22137 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22137step0 raw22137; decide +kernel
      have hl : raw22137step0Labels = raw22137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22137 raw22137Labels permutation434 hz
    mixedMoment B raw22137step0 raw22137step0Labels = mixedMoment B raw22137step1 raw22137step1Labels := by
      have ha : raw22137step1 = (fun i j => raw22137step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22137step1 raw22137step0; decide +kernel
      have hl : raw22137step1Labels = raw22137step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22137step0 raw22137step0Labels permutation38 permutation2
    _ = mixedMoment B node4218 node4218Labels := by rfl

def raw22138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22138 raw22138Labels = mixedMoment B node4218 node4218Labels := by
  calc
    mixedMoment B raw22138 raw22138Labels = mixedMoment B raw22138step0 raw22138step0Labels := by
      have hz : ∀ j, raw22138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22138step0 = (fun i j => raw22138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22138step0 raw22138; decide +kernel
      have hl : raw22138step0Labels = raw22138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22138 raw22138Labels permutation346 hz
    mixedMoment B raw22138step0 raw22138step0Labels = mixedMoment B raw22138step1 raw22138step1Labels := by
      have ha : raw22138step1 = (fun i j => raw22138step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22138step1 raw22138step0; decide +kernel
      have hl : raw22138step1Labels = raw22138step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22138step0 raw22138step0Labels permutation38 permutation2
    _ = mixedMoment B node4218 node4218Labels := by rfl

def raw22139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw22139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw22139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw22139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22139 raw22139Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw22139 raw22139Labels = mixedMoment B raw22139step0 raw22139step0Labels := by
      have hz : ∀ j, raw22139 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22139step0 = (fun i j => raw22139 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22139step0 raw22139; decide +kernel
      have hl : raw22139step0Labels = raw22139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22139 raw22139Labels permutation434 hz
    mixedMoment B raw22139step0 raw22139step0Labels = mixedMoment B raw22139step1 raw22139step1Labels := by
      have hz : ∀ j, raw22139step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22139step1 = (fun i j => raw22139step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22139step1 raw22139step0; decide +kernel
      have hl : raw22139step1Labels = raw22139step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22139step0 raw22139step0Labels permutation80 hz
    mixedMoment B raw22139step1 raw22139step1Labels = mixedMoment B raw22139step2 raw22139step2Labels := by
      have ha : raw22139step2 = (fun i j => raw22139step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22139step2 raw22139step1; decide +kernel
      have hl : raw22139step2Labels = raw22139step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22139step1 raw22139step1Labels permutation10 permutation2
    _ = mixedMoment B node4269 node4269Labels := by rfl

def raw22140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw22140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22140step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22140step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw22140step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22140step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22140 raw22140Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22140 raw22140Labels = mixedMoment B raw22140step0 raw22140step0Labels := by
      have hz : ∀ j, raw22140 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22140step0 = (fun i j => raw22140 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22140step0 raw22140; decide +kernel
      have hl : raw22140step0Labels = raw22140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22140 raw22140Labels permutation434 hz
    mixedMoment B raw22140step0 raw22140step0Labels = mixedMoment B raw22140step1 raw22140step1Labels := by
      have hz : ∀ j, raw22140step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22140step1 = (fun i j => raw22140step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22140step1 raw22140step0; decide +kernel
      have hl : raw22140step1Labels = raw22140step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22140step0 raw22140step0Labels permutation80 hz
    mixedMoment B raw22140step1 raw22140step1Labels = mixedMoment B raw22140step2 raw22140step2Labels := by
      have hz : ∀ i, raw22140step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw22140step2 = (fun i j => raw22140step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw22140step2 raw22140step1; decide +kernel
      have hl : raw22140step2Labels = (fun j => raw22140step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22140step1 raw22140step1Labels permutation4 hz
    mixedMoment B raw22140step2 raw22140step2Labels = mixedMoment B raw22140step3 raw22140step3Labels := by
      have ha : raw22140step3 = raw22140step2 := by apply Matrix.ext; unfold raw22140step3 raw22140step2; decide +kernel
      have hl : raw22140step2Labels = labelEmbedding2 ∘ raw22140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22140step2 raw22140step2Labels raw22140step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw22141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22141 raw22141Labels = mixedMoment B node4101 node4101Labels := by
  calc
    mixedMoment B raw22141 raw22141Labels = mixedMoment B raw22141step0 raw22141step0Labels := by
      have hz : ∀ j, raw22141 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22141step0 = (fun i j => raw22141 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22141step0 raw22141; decide +kernel
      have hl : raw22141step0Labels = raw22141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22141 raw22141Labels permutation434 hz
    _ = mixedMoment B node4101 node4101Labels := by rfl

def raw22142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22142 raw22142Labels = mixedMoment B node4233 node4233Labels := by
  calc
    mixedMoment B raw22142 raw22142Labels = mixedMoment B raw22142step0 raw22142step0Labels := by
      have hz : ∀ j, raw22142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22142step0 = (fun i j => raw22142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22142step0 raw22142; decide +kernel
      have hl : raw22142step0Labels = raw22142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22142 raw22142Labels permutation434 hz
    _ = mixedMoment B node4233 node4233Labels := by rfl

def raw22143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw22143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22143 raw22143Labels = mixedMoment B node4196 node4196Labels := by
  calc
    mixedMoment B raw22143 raw22143Labels = mixedMoment B raw22143step0 raw22143step0Labels := by
      have ha : raw22143step0 = (fun i j => raw22143 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22143step0 raw22143; decide +kernel
      have hl : raw22143step0Labels = raw22143Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22143 raw22143Labels permutation200 permutation2
    _ = mixedMoment B node4196 node4196Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
