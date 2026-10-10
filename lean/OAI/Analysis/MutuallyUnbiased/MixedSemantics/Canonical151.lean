import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19328 raw19328Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw19328 raw19328Labels = mixedMoment B raw19328step0 raw19328step0Labels := by
      have ha : raw19328step0 = (fun i j => raw19328 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19328step0 raw19328; decide +kernel
      have hl : raw19328step0Labels = raw19328Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19328 raw19328Labels permutation156 permutation2
    _ = mixedMoment B node5386 node5386Labels := by rfl

def raw19329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19329 raw19329Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw19329 raw19329Labels = mixedMoment B raw19329step0 raw19329step0Labels := by
      have ha : raw19329step0 = (fun i j => raw19329 (permutation165 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19329step0 raw19329; decide +kernel
      have hl : raw19329step0Labels = raw19329Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19329 raw19329Labels permutation165 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw19330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19330 raw19330Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw19330 raw19330Labels = mixedMoment B raw19330step0 raw19330step0Labels := by
      have hz : ∀ j, raw19330 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19330step0 = (fun i j => raw19330 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19330step0 raw19330; decide +kernel
      have hl : raw19330step0Labels = raw19330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19330 raw19330Labels permutation590 hz
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw19331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19331step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19331 raw19331Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw19331 raw19331Labels = mixedMoment B raw19331step0 raw19331step0Labels := by
      have hz : ∀ j, raw19331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19331step0 = (fun i j => raw19331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19331step0 raw19331; decide +kernel
      have hl : raw19331step0Labels = raw19331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19331 raw19331Labels permutation346 hz
    mixedMoment B raw19331step0 raw19331step0Labels = mixedMoment B raw19331step1 raw19331step1Labels := by
      have ha : raw19331step1 = (fun i j => raw19331step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19331step1 raw19331step0; decide +kernel
      have hl : raw19331step1Labels = raw19331step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19331step0 raw19331step0Labels permutation37 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw19332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19332 raw19332Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw19332 raw19332Labels = mixedMoment B raw19332step0 raw19332step0Labels := by
      have ha : raw19332step0 = (fun i j => raw19332 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19332step0 raw19332; decide +kernel
      have hl : raw19332step0Labels = raw19332Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19332 raw19332Labels permutation157 permutation2
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw19333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19333 raw19333Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw19333 raw19333Labels = mixedMoment B raw19333step0 raw19333step0Labels := by
      have hz : ∀ j, raw19333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19333step0 = (fun i j => raw19333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19333step0 raw19333; decide +kernel
      have hl : raw19333step0Labels = raw19333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19333 raw19333Labels permutation346 hz
    mixedMoment B raw19333step0 raw19333step0Labels = mixedMoment B raw19333step1 raw19333step1Labels := by
      have ha : raw19333step1 = (fun i j => raw19333step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19333step1 raw19333step0; decide +kernel
      have hl : raw19333step1Labels = raw19333step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19333step0 raw19333step0Labels permutation35 permutation2
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw19334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw19334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw19334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19334step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19334 raw19334Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw19334 raw19334Labels = mixedMoment B raw19334step0 raw19334step0Labels := by
      have hz : ∀ j, raw19334 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19334step0 = (fun i j => raw19334 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19334step0 raw19334; decide +kernel
      have hl : raw19334step0Labels = raw19334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19334 raw19334Labels permutation590 hz
    mixedMoment B raw19334step0 raw19334step0Labels = mixedMoment B raw19334step1 raw19334step1Labels := by
      have hz : ∀ j, raw19334step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19334step1 = (fun i j => raw19334step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19334step1 raw19334step0; decide +kernel
      have hl : raw19334step1Labels = raw19334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19334step0 raw19334step0Labels permutation80 hz
    mixedMoment B raw19334step1 raw19334step1Labels = mixedMoment B raw19334step2 raw19334step2Labels := by
      have ha : raw19334step2 = (fun i j => raw19334step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19334step2 raw19334step1; decide +kernel
      have hl : raw19334step2Labels = raw19334step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19334step1 raw19334step1Labels permutation9 permutation2
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw19335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19335step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19335 raw19335Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw19335 raw19335Labels = mixedMoment B raw19335step0 raw19335step0Labels := by
      have hz : ∀ j, raw19335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19335step0 = (fun i j => raw19335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19335step0 raw19335; decide +kernel
      have hl : raw19335step0Labels = raw19335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19335 raw19335Labels permutation346 hz
    mixedMoment B raw19335step0 raw19335step0Labels = mixedMoment B raw19335step1 raw19335step1Labels := by
      have ha : raw19335step1 = (fun i j => raw19335step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19335step1 raw19335step0; decide +kernel
      have hl : raw19335step1Labels = raw19335step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19335step0 raw19335step0Labels permutation36 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw19336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19336 raw19336Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw19336 raw19336Labels = mixedMoment B raw19336step0 raw19336step0Labels := by
      have ha : raw19336step0 = (fun i j => raw19336 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19336step0 raw19336; decide +kernel
      have hl : raw19336step0Labels = raw19336Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19336 raw19336Labels permutation156 permutation2
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw19337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw19337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19337 raw19337Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw19337 raw19337Labels = mixedMoment B raw19337step0 raw19337step0Labels := by
      have hz : ∀ j, raw19337 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19337step0 = (fun i j => raw19337 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19337step0 raw19337; decide +kernel
      have hl : raw19337step0Labels = raw19337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19337 raw19337Labels permutation590 hz
    mixedMoment B raw19337step0 raw19337step0Labels = mixedMoment B raw19337step1 raw19337step1Labels := by
      have hz : ∀ j, raw19337step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19337step1 = (fun i j => raw19337step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19337step1 raw19337step0; decide +kernel
      have hl : raw19337step1Labels = raw19337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19337step0 raw19337step0Labels permutation80 hz
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw19338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19338step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19338 raw19338Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw19338 raw19338Labels = mixedMoment B raw19338step0 raw19338step0Labels := by
      have ha : raw19338step0 = (fun i j => raw19338 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19338step0 raw19338; decide +kernel
      have hl : raw19338step0Labels = raw19338Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19338 raw19338Labels permutation265 permutation3
    mixedMoment B raw19338step0 raw19338step0Labels = mixedMoment B raw19338step1 raw19338step1Labels := by
      have ha : raw19338step1 = raw19338step0 := by apply Matrix.ext; unfold raw19338step1 raw19338step0; decide +kernel
      have hl : raw19338step0Labels = labelEmbedding6 ∘ raw19338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19338step0 raw19338step0Labels raw19338step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw19339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19339step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19339step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19339step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19339step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19339step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19339 raw19339Labels = mixedMoment B node5479 node5479Labels := by
  calc
    mixedMoment B raw19339 raw19339Labels = mixedMoment B raw19339step0 raw19339step0Labels := by
      have ha : raw19339step0 = (fun i j => raw19339 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19339step0 raw19339; decide +kernel
      have hl : raw19339step0Labels = raw19339Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19339 raw19339Labels permutation176 permutation7
    mixedMoment B raw19339step0 raw19339step0Labels = mixedMoment B raw19339step1 raw19339step1Labels := by
      have ha : raw19339step1 = -raw19339step0 := by apply Matrix.ext; change ∀ i j, raw19339step1 i j = -(raw19339step0 i j); unfold raw19339step1 raw19339step0; decide +kernel
      have hl : raw19339step1Labels = raw19339step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19339step1 raw19339step1Labels = mixedMoment B raw19339step2 raw19339step2Labels := by
      have ha : raw19339step2 = raw19339step1 := by apply Matrix.ext; unfold raw19339step2 raw19339step1; decide +kernel
      have hl : raw19339step1Labels = labelEmbedding10 ∘ raw19339step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19339step1 raw19339step1Labels raw19339step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5479 node5479Labels := by rfl

def raw19340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19340step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19340step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19340step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19340step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19340 raw19340Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19340 raw19340Labels = mixedMoment B raw19340step0 raw19340step0Labels := by
      have ha : raw19340step0 = (fun i j => raw19340 (permutation179 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19340step0 raw19340; decide +kernel
      have hl : raw19340step0Labels = raw19340Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19340 raw19340Labels permutation179 permutation6
    mixedMoment B raw19340step0 raw19340step0Labels = mixedMoment B raw19340step1 raw19340step1Labels := by
      have ha : raw19340step1 = -raw19340step0 := by apply Matrix.ext; change ∀ i j, raw19340step1 i j = -(raw19340step0 i j); unfold raw19340step1 raw19340step0; decide +kernel
      have hl : raw19340step1Labels = raw19340step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19340step1 raw19340step1Labels = mixedMoment B raw19340step2 raw19340step2Labels := by
      have ha : raw19340step2 = raw19340step1 := by apply Matrix.ext; unfold raw19340step2 raw19340step1; decide +kernel
      have hl : raw19340step1Labels = labelEmbedding9 ∘ raw19340step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19340step1 raw19340step1Labels raw19340step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw19341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19341step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19341step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19341step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19341 raw19341Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19341 raw19341Labels = mixedMoment B raw19341step0 raw19341step0Labels := by
      have ha : raw19341step0 = (fun i j => raw19341 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19341step0 raw19341; decide +kernel
      have hl : raw19341step0Labels = raw19341Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19341 raw19341Labels permutation177 permutation6
    mixedMoment B raw19341step0 raw19341step0Labels = mixedMoment B raw19341step1 raw19341step1Labels := by
      have ha : raw19341step1 = -raw19341step0 := by apply Matrix.ext; change ∀ i j, raw19341step1 i j = -(raw19341step0 i j); unfold raw19341step1 raw19341step0; decide +kernel
      have hl : raw19341step1Labels = raw19341step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19341step1 raw19341step1Labels = mixedMoment B raw19341step2 raw19341step2Labels := by
      have ha : raw19341step2 = raw19341step1 := by apply Matrix.ext; unfold raw19341step2 raw19341step1; decide +kernel
      have hl : raw19341step1Labels = labelEmbedding9 ∘ raw19341step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19341step1 raw19341step1Labels raw19341step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw19342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19342step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19342step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19342step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19342step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19342step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19342 raw19342Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19342 raw19342Labels = mixedMoment B raw19342step0 raw19342step0Labels := by
      have ha : raw19342step0 = (fun i j => raw19342 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19342step0 raw19342; decide +kernel
      have hl : raw19342step0Labels = raw19342Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19342 raw19342Labels permutation176 permutation6
    mixedMoment B raw19342step0 raw19342step0Labels = mixedMoment B raw19342step1 raw19342step1Labels := by
      have ha : raw19342step1 = -raw19342step0 := by apply Matrix.ext; change ∀ i j, raw19342step1 i j = -(raw19342step0 i j); unfold raw19342step1 raw19342step0; decide +kernel
      have hl : raw19342step1Labels = raw19342step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19342step1 raw19342step1Labels = mixedMoment B raw19342step2 raw19342step2Labels := by
      have ha : raw19342step2 = raw19342step1 := by apply Matrix.ext; unfold raw19342step2 raw19342step1; decide +kernel
      have hl : raw19342step1Labels = labelEmbedding9 ∘ raw19342step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19342step1 raw19342step1Labels raw19342step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19343 raw19343Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw19343 raw19343Labels = mixedMoment B raw19343step0 raw19343step0Labels := by
      have hz : ∀ j, raw19343 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19343step0 = (fun i j => raw19343 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19343step0 raw19343; decide +kernel
      have hl : raw19343step0Labels = raw19343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19343 raw19343Labels permutation265 hz
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw19344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19344 raw19344Labels = mixedMoment B node5383 node5383Labels := by
  calc
    _ = mixedMoment B node5383 node5383Labels := by rfl

def raw19345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19345 raw19345Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw19345 raw19345Labels = mixedMoment B raw19345step0 raw19345step0Labels := by
      have ha : raw19345step0 = (fun i j => raw19345 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19345step0 raw19345; decide +kernel
      have hl : raw19345step0Labels = raw19345Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19345 raw19345Labels permutation158 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw19346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw19346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19346 raw19346Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw19346 raw19346Labels = mixedMoment B raw19346step0 raw19346step0Labels := by
      have ha : raw19346step0 = (fun i j => raw19346 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19346step0 raw19346; decide +kernel
      have hl : raw19346step0Labels = raw19346Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19346 raw19346Labels permutation164 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw19347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw19347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19347 raw19347Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw19347 raw19347Labels = mixedMoment B raw19347step0 raw19347step0Labels := by
      have ha : raw19347step0 = (fun i j => raw19347 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19347step0 raw19347; decide +kernel
      have hl : raw19347step0Labels = raw19347Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19347 raw19347Labels permutation170 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw19348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19348 raw19348Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw19348 raw19348Labels = mixedMoment B raw19348step0 raw19348step0Labels := by
      have ha : raw19348step0 = (fun i j => raw19348 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19348step0 raw19348; decide +kernel
      have hl : raw19348step0Labels = raw19348Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19348 raw19348Labels permutation155 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw19349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19349 raw19349Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw19349 raw19349Labels = mixedMoment B raw19349step0 raw19349step0Labels := by
      have ha : raw19349step0 = (fun i j => raw19349 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19349step0 raw19349; decide +kernel
      have hl : raw19349step0Labels = raw19349Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19349 raw19349Labels permutation179 permutation2
    _ = mixedMoment B node5396 node5396Labels := by rfl

def raw19350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw19350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19350 raw19350Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw19350 raw19350Labels = mixedMoment B raw19350step0 raw19350step0Labels := by
      have ha : raw19350step0 = (fun i j => raw19350 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19350step0 raw19350; decide +kernel
      have hl : raw19350step0Labels = raw19350Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19350 raw19350Labels permutation155 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw19351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw19351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19351 raw19351Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw19351 raw19351Labels = mixedMoment B raw19351step0 raw19351step0Labels := by
      have ha : raw19351step0 = (fun i j => raw19351 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19351step0 raw19351; decide +kernel
      have hl : raw19351step0Labels = raw19351Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19351 raw19351Labels permutation157 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw19352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw19352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19352 raw19352Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw19352 raw19352Labels = mixedMoment B raw19352step0 raw19352step0Labels := by
      have ha : raw19352step0 = (fun i j => raw19352 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19352step0 raw19352; decide +kernel
      have hl : raw19352step0Labels = raw19352Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19352 raw19352Labels permutation153 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw19353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw19353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19353 raw19353Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw19353 raw19353Labels = mixedMoment B raw19353step0 raw19353step0Labels := by
      have ha : raw19353step0 = (fun i j => raw19353 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19353step0 raw19353; decide +kernel
      have hl : raw19353step0Labels = raw19353Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19353 raw19353Labels permutation177 permutation2
    _ = mixedMoment B node5396 node5396Labels := by rfl

def raw19354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw19354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19354 raw19354Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw19354 raw19354Labels = mixedMoment B raw19354step0 raw19354step0Labels := by
      have ha : raw19354step0 = (fun i j => raw19354 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19354step0 raw19354; decide +kernel
      have hl : raw19354step0Labels = raw19354Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19354 raw19354Labels permutation153 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw19355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw19355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19355 raw19355Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw19355 raw19355Labels = mixedMoment B raw19355step0 raw19355step0Labels := by
      have ha : raw19355step0 = (fun i j => raw19355 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19355step0 raw19355; decide +kernel
      have hl : raw19355step0Labels = raw19355Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19355 raw19355Labels permutation156 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw19356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19356 raw19356Labels = mixedMoment B node5380 node5380Labels := by
  calc
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw19357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19357 raw19357Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw19357 raw19357Labels = mixedMoment B raw19357step0 raw19357step0Labels := by
      have ha : raw19357step0 = (fun i j => raw19357 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19357step0 raw19357; decide +kernel
      have hl : raw19357step0Labels = raw19357Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19357 raw19357Labels permutation176 permutation2
    _ = mixedMoment B node5396 node5396Labels := by rfl

def raw19358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19358 raw19358Labels = mixedMoment B node5424 node5424Labels := by
  calc
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw19359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw19359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19359 raw19359Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw19359 raw19359Labels = mixedMoment B raw19359step0 raw19359step0Labels := by
      have ha : raw19359step0 = (fun i j => raw19359 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19359step0 raw19359; decide +kernel
      have hl : raw19359step0Labels = raw19359Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19359 raw19359Labels permutation154 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw19360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19360step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw19360step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19360 raw19360Labels = mixedMoment B node4087 node4087Labels := by
  calc
    mixedMoment B raw19360 raw19360Labels = mixedMoment B raw19360step0 raw19360step0Labels := by
      have hz : ∀ i, raw19360 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19360step0 = (fun i j => raw19360 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19360step0 raw19360; decide +kernel
      have hl : raw19360step0Labels = (fun j => raw19360Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19360 raw19360Labels permutation6 hz
    _ = mixedMoment B node4087 node4087Labels := by rfl

def raw19361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw19361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19361step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19361step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19361 raw19361Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19361 raw19361Labels = mixedMoment B raw19361step0 raw19361step0Labels := by
      have hz : ∀ j, raw19361 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19361step0 = (fun i j => raw19361 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19361step0 raw19361; decide +kernel
      have hl : raw19361step0Labels = raw19361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19361 raw19361Labels permutation520 hz
    mixedMoment B raw19361step0 raw19361step0Labels = mixedMoment B raw19361step1 raw19361step1Labels := by
      have hz : ∀ i, raw19361step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19361step1 = (fun i j => raw19361step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19361step1 raw19361step0; decide +kernel
      have hl : raw19361step1Labels = (fun j => raw19361step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19361step0 raw19361step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw19362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw19362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19362step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19362step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19362 raw19362Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19362 raw19362Labels = mixedMoment B raw19362step0 raw19362step0Labels := by
      have hz : ∀ j, raw19362 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19362step0 = (fun i j => raw19362 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19362step0 raw19362; decide +kernel
      have hl : raw19362step0Labels = raw19362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19362 raw19362Labels permutation590 hz
    mixedMoment B raw19362step0 raw19362step0Labels = mixedMoment B raw19362step1 raw19362step1Labels := by
      have hz : ∀ i, raw19362step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19362step1 = (fun i j => raw19362step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19362step1 raw19362step0; decide +kernel
      have hl : raw19362step1Labels = (fun j => raw19362step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19362step0 raw19362step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw19363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19363step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw19363step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19363step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw19363step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19363 raw19363Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw19363 raw19363Labels = mixedMoment B raw19363step0 raw19363step0Labels := by
      have hz : ∀ j, raw19363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19363step0 = (fun i j => raw19363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19363step0 raw19363; decide +kernel
      have hl : raw19363step0Labels = raw19363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19363 raw19363Labels permutation346 hz
    mixedMoment B raw19363step0 raw19363step0Labels = mixedMoment B raw19363step1 raw19363step1Labels := by
      have hz : ∀ i, raw19363step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19363step1 = (fun i j => raw19363step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19363step1 raw19363step0; decide +kernel
      have hl : raw19363step1Labels = (fun j => raw19363step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19363step0 raw19363step0Labels permutation6 hz
    mixedMoment B raw19363step1 raw19363step1Labels = mixedMoment B raw19363step2 raw19363step2Labels := by
      have ha : raw19363step2 = (fun i j => raw19363step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19363step2 raw19363step1; decide +kernel
      have hl : raw19363step2Labels = raw19363step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19363step1 raw19363step1Labels permutation35 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw19364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19364step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw19364step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19364step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19364step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19364 raw19364Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19364 raw19364Labels = mixedMoment B raw19364step0 raw19364step0Labels := by
      have hz : ∀ i, raw19364 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19364step0 = (fun i j => raw19364 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19364step0 raw19364; decide +kernel
      have hl : raw19364step0Labels = (fun j => raw19364Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19364 raw19364Labels permutation6 hz
    mixedMoment B raw19364step0 raw19364step0Labels = mixedMoment B raw19364step1 raw19364step1Labels := by
      have ha : raw19364step1 = (fun i j => raw19364step0 (permutation155 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19364step1 raw19364step0; decide +kernel
      have hl : raw19364step1Labels = raw19364step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19364step0 raw19364step0Labels permutation155 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw19365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw19365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19365step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19365step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw19365step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19365step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw19365step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19365 raw19365Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw19365 raw19365Labels = mixedMoment B raw19365step0 raw19365step0Labels := by
      have hz : ∀ j, raw19365 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19365step0 = (fun i j => raw19365 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19365step0 raw19365; decide +kernel
      have hl : raw19365step0Labels = raw19365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19365 raw19365Labels permutation520 hz
    mixedMoment B raw19365step0 raw19365step0Labels = mixedMoment B raw19365step1 raw19365step1Labels := by
      have hz : ∀ j, raw19365step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19365step1 = (fun i j => raw19365step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19365step1 raw19365step0; decide +kernel
      have hl : raw19365step1Labels = raw19365step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19365step0 raw19365step0Labels permutation80 hz
    mixedMoment B raw19365step1 raw19365step1Labels = mixedMoment B raw19365step2 raw19365step2Labels := by
      have hz : ∀ i, raw19365step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19365step2 = (fun i j => raw19365step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19365step2 raw19365step1; decide +kernel
      have hl : raw19365step2Labels = (fun j => raw19365step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19365step1 raw19365step1Labels permutation6 hz
    mixedMoment B raw19365step2 raw19365step2Labels = mixedMoment B raw19365step3 raw19365step3Labels := by
      have ha : raw19365step3 = (fun i j => raw19365step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19365step3 raw19365step2; decide +kernel
      have hl : raw19365step3Labels = raw19365step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19365step2 raw19365step2Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw19366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw19366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19366step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19366step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw19366step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19366step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw19366step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19366 raw19366Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw19366 raw19366Labels = mixedMoment B raw19366step0 raw19366step0Labels := by
      have hz : ∀ j, raw19366 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19366step0 = (fun i j => raw19366 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19366step0 raw19366; decide +kernel
      have hl : raw19366step0Labels = raw19366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19366 raw19366Labels permutation590 hz
    mixedMoment B raw19366step0 raw19366step0Labels = mixedMoment B raw19366step1 raw19366step1Labels := by
      have hz : ∀ j, raw19366step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19366step1 = (fun i j => raw19366step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19366step1 raw19366step0; decide +kernel
      have hl : raw19366step1Labels = raw19366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19366step0 raw19366step0Labels permutation80 hz
    mixedMoment B raw19366step1 raw19366step1Labels = mixedMoment B raw19366step2 raw19366step2Labels := by
      have hz : ∀ i, raw19366step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19366step2 = (fun i j => raw19366step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19366step2 raw19366step1; decide +kernel
      have hl : raw19366step2Labels = (fun j => raw19366step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19366step1 raw19366step1Labels permutation6 hz
    mixedMoment B raw19366step2 raw19366step2Labels = mixedMoment B raw19366step3 raw19366step3Labels := by
      have ha : raw19366step3 = (fun i j => raw19366step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19366step3 raw19366step2; decide +kernel
      have hl : raw19366step3Labels = raw19366step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19366step2 raw19366step2Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw19367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19367step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw19367step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19367step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw19367step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19367 raw19367Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw19367 raw19367Labels = mixedMoment B raw19367step0 raw19367step0Labels := by
      have hz : ∀ j, raw19367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19367step0 = (fun i j => raw19367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19367step0 raw19367; decide +kernel
      have hl : raw19367step0Labels = raw19367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19367 raw19367Labels permutation346 hz
    mixedMoment B raw19367step0 raw19367step0Labels = mixedMoment B raw19367step1 raw19367step1Labels := by
      have hz : ∀ i, raw19367step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19367step1 = (fun i j => raw19367step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19367step1 raw19367step0; decide +kernel
      have hl : raw19367step1Labels = (fun j => raw19367step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19367step0 raw19367step0Labels permutation6 hz
    mixedMoment B raw19367step1 raw19367step1Labels = mixedMoment B raw19367step2 raw19367step2Labels := by
      have ha : raw19367step2 = (fun i j => raw19367step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19367step2 raw19367step1; decide +kernel
      have hl : raw19367step2Labels = raw19367step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19367step1 raw19367step1Labels permutation33 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw19368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19368step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw19368step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19368step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19368step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19368 raw19368Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19368 raw19368Labels = mixedMoment B raw19368step0 raw19368step0Labels := by
      have hz : ∀ i, raw19368 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19368step0 = (fun i j => raw19368 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19368step0 raw19368; decide +kernel
      have hl : raw19368step0Labels = (fun j => raw19368Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19368 raw19368Labels permutation6 hz
    mixedMoment B raw19368step0 raw19368step0Labels = mixedMoment B raw19368step1 raw19368step1Labels := by
      have ha : raw19368step1 = (fun i j => raw19368step0 (permutation153 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19368step1 raw19368step0; decide +kernel
      have hl : raw19368step1Labels = raw19368step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19368step0 raw19368step0Labels permutation153 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw19369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw19369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw19369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19369step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw19369step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19369step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw19369step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19369 raw19369Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw19369 raw19369Labels = mixedMoment B raw19369step0 raw19369step0Labels := by
      have hz : ∀ j, raw19369 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19369step0 = (fun i j => raw19369 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19369step0 raw19369; decide +kernel
      have hl : raw19369step0Labels = raw19369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19369 raw19369Labels permutation590 hz
    mixedMoment B raw19369step0 raw19369step0Labels = mixedMoment B raw19369step1 raw19369step1Labels := by
      have hz : ∀ j, raw19369step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19369step1 = (fun i j => raw19369step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19369step1 raw19369step0; decide +kernel
      have hl : raw19369step1Labels = raw19369step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19369step0 raw19369step0Labels permutation80 hz
    mixedMoment B raw19369step1 raw19369step1Labels = mixedMoment B raw19369step2 raw19369step2Labels := by
      have hz : ∀ i, raw19369step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19369step2 = (fun i j => raw19369step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19369step2 raw19369step1; decide +kernel
      have hl : raw19369step2Labels = (fun j => raw19369step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19369step1 raw19369step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw19370 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19370step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19370step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19370step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19370step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19370 raw19370Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw19370 raw19370Labels = mixedMoment B raw19370step0 raw19370step0Labels := by
      have ha : raw19370step0 = (fun i j => raw19370 (permutation304 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19370step0 raw19370; decide +kernel
      have hl : raw19370step0Labels = raw19370Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19370 raw19370Labels permutation304 permutation5
    mixedMoment B raw19370step0 raw19370step0Labels = mixedMoment B raw19370step1 raw19370step1Labels := by
      have ha : raw19370step1 = -raw19370step0 := by apply Matrix.ext; change ∀ i j, raw19370step1 i j = -(raw19370step0 i j); unfold raw19370step1 raw19370step0; decide +kernel
      have hl : raw19370step1Labels = raw19370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19370step1 raw19370step1Labels = mixedMoment B raw19370step2 raw19370step2Labels := by
      have ha : raw19370step2 = raw19370step1 := by apply Matrix.ext; unfold raw19370step2 raw19370step1; decide +kernel
      have hl : raw19370step1Labels = labelEmbedding8 ∘ raw19370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19370step1 raw19370step1Labels raw19370step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw19371 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19371step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19371step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19371step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19371step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19371 raw19371Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw19371 raw19371Labels = mixedMoment B raw19371step0 raw19371step0Labels := by
      have ha : raw19371step0 = (fun i j => raw19371 (permutation381 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19371step0 raw19371; decide +kernel
      have hl : raw19371step0Labels = raw19371Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19371 raw19371Labels permutation381 permutation5
    mixedMoment B raw19371step0 raw19371step0Labels = mixedMoment B raw19371step1 raw19371step1Labels := by
      have ha : raw19371step1 = -raw19371step0 := by apply Matrix.ext; change ∀ i j, raw19371step1 i j = -(raw19371step0 i j); unfold raw19371step1 raw19371step0; decide +kernel
      have hl : raw19371step1Labels = raw19371step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19371step1 raw19371step1Labels = mixedMoment B raw19371step2 raw19371step2Labels := by
      have ha : raw19371step2 = raw19371step1 := by apply Matrix.ext; unfold raw19371step2 raw19371step1; decide +kernel
      have hl : raw19371step1Labels = labelEmbedding8 ∘ raw19371step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19371step1 raw19371step1Labels raw19371step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw19372 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19372step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19372step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19372step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19372 raw19372Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw19372 raw19372Labels = mixedMoment B raw19372step0 raw19372step0Labels := by
      have hz : ∀ j, raw19372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19372step0 = (fun i j => raw19372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19372step0 raw19372; decide +kernel
      have hl : raw19372step0Labels = raw19372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19372 raw19372Labels permutation434 hz
    mixedMoment B raw19372step0 raw19372step0Labels = mixedMoment B raw19372step1 raw19372step1Labels := by
      have ha : raw19372step1 = (fun i j => raw19372step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19372step1 raw19372step0; decide +kernel
      have hl : raw19372step1Labels = raw19372step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19372step0 raw19372step0Labels permutation44 permutation4
    mixedMoment B raw19372step1 raw19372step1Labels = mixedMoment B raw19372step2 raw19372step2Labels := by
      have ha : raw19372step2 = raw19372step1 := by apply Matrix.ext; unfold raw19372step2 raw19372step1; decide +kernel
      have hl : raw19372step1Labels = labelEmbedding7 ∘ raw19372step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19372step1 raw19372step1Labels raw19372step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw19373 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19373step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19373step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19373step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19373 raw19373Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw19373 raw19373Labels = mixedMoment B raw19373step0 raw19373step0Labels := by
      have hz : ∀ j, raw19373 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19373step0 = (fun i j => raw19373 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19373step0 raw19373; decide +kernel
      have hl : raw19373step0Labels = raw19373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19373 raw19373Labels permutation520 hz
    mixedMoment B raw19373step0 raw19373step0Labels = mixedMoment B raw19373step1 raw19373step1Labels := by
      have ha : raw19373step1 = (fun i j => raw19373step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19373step1 raw19373step0; decide +kernel
      have hl : raw19373step1Labels = raw19373step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19373step0 raw19373step0Labels permutation44 permutation4
    mixedMoment B raw19373step1 raw19373step1Labels = mixedMoment B raw19373step2 raw19373step2Labels := by
      have ha : raw19373step2 = raw19373step1 := by apply Matrix.ext; unfold raw19373step2 raw19373step1; decide +kernel
      have hl : raw19373step1Labels = labelEmbedding7 ∘ raw19373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19373step1 raw19373step1Labels raw19373step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw19374 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19374step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19374step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19374 raw19374Labels = mixedMoment B node5415 node5415Labels := by
  calc
    mixedMoment B raw19374 raw19374Labels = mixedMoment B raw19374step0 raw19374step0Labels := by
      have ha : raw19374step0 = (fun i j => raw19374 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19374step0 raw19374; decide +kernel
      have hl : raw19374step0Labels = raw19374Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19374 raw19374Labels permutation212 permutation4
    mixedMoment B raw19374step0 raw19374step0Labels = mixedMoment B raw19374step1 raw19374step1Labels := by
      have ha : raw19374step1 = raw19374step0 := by apply Matrix.ext; unfold raw19374step1 raw19374step0; decide +kernel
      have hl : raw19374step0Labels = labelEmbedding7 ∘ raw19374step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19374step0 raw19374step0Labels raw19374step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5415 node5415Labels := by rfl

def raw19375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19375step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19375step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19375step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19375 raw19375Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw19375 raw19375Labels = mixedMoment B raw19375step0 raw19375step0Labels := by
      have hz : ∀ j, raw19375 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19375step0 = (fun i j => raw19375 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19375step0 raw19375; decide +kernel
      have hl : raw19375step0Labels = raw19375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19375 raw19375Labels permutation265 hz
    mixedMoment B raw19375step0 raw19375step0Labels = mixedMoment B raw19375step1 raw19375step1Labels := by
      have ha : raw19375step1 = (fun i j => raw19375step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19375step1 raw19375step0; decide +kernel
      have hl : raw19375step1Labels = raw19375step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19375step0 raw19375step0Labels permutation60 permutation3
    mixedMoment B raw19375step1 raw19375step1Labels = mixedMoment B raw19375step2 raw19375step2Labels := by
      have ha : raw19375step2 = raw19375step1 := by apply Matrix.ext; unfold raw19375step2 raw19375step1; decide +kernel
      have hl : raw19375step1Labels = labelEmbedding6 ∘ raw19375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19375step1 raw19375step1Labels raw19375step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw19376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19376step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19376step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19376step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19376step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19376step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19376 raw19376Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw19376 raw19376Labels = mixedMoment B raw19376step0 raw19376step0Labels := by
      have hz : ∀ j, raw19376 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19376step0 = (fun i j => raw19376 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19376step0 raw19376; decide +kernel
      have hl : raw19376step0Labels = raw19376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19376 raw19376Labels permutation434 hz
    mixedMoment B raw19376step0 raw19376step0Labels = mixedMoment B raw19376step1 raw19376step1Labels := by
      have hz : ∀ j, raw19376step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19376step1 = (fun i j => raw19376step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19376step1 raw19376step0; decide +kernel
      have hl : raw19376step1Labels = raw19376step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19376step0 raw19376step0Labels permutation56 hz
    mixedMoment B raw19376step1 raw19376step1Labels = mixedMoment B raw19376step2 raw19376step2Labels := by
      have ha : raw19376step2 = (fun i j => raw19376step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19376step2 raw19376step1; decide +kernel
      have hl : raw19376step2Labels = raw19376step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19376step1 raw19376step1Labels permutation29 permutation6
    mixedMoment B raw19376step2 raw19376step2Labels = mixedMoment B raw19376step3 raw19376step3Labels := by
      have ha : raw19376step3 = raw19376step2 := by apply Matrix.ext; unfold raw19376step3 raw19376step2; decide +kernel
      have hl : raw19376step2Labels = labelEmbedding9 ∘ raw19376step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19376step2 raw19376step2Labels raw19376step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw19377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19377step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19377step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19377step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19377step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw19377step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19377 raw19377Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw19377 raw19377Labels = mixedMoment B raw19377step0 raw19377step0Labels := by
      have hz : ∀ j, raw19377 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19377step0 = (fun i j => raw19377 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19377step0 raw19377; decide +kernel
      have hl : raw19377step0Labels = raw19377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19377 raw19377Labels permutation520 hz
    mixedMoment B raw19377step0 raw19377step0Labels = mixedMoment B raw19377step1 raw19377step1Labels := by
      have hz : ∀ j, raw19377step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19377step1 = (fun i j => raw19377step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19377step1 raw19377step0; decide +kernel
      have hl : raw19377step1Labels = raw19377step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19377step0 raw19377step0Labels permutation56 hz
    mixedMoment B raw19377step1 raw19377step1Labels = mixedMoment B raw19377step2 raw19377step2Labels := by
      have ha : raw19377step2 = (fun i j => raw19377step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19377step2 raw19377step1; decide +kernel
      have hl : raw19377step2Labels = raw19377step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19377step1 raw19377step1Labels permutation29 permutation6
    mixedMoment B raw19377step2 raw19377step2Labels = mixedMoment B raw19377step3 raw19377step3Labels := by
      have ha : raw19377step3 = raw19377step2 := by apply Matrix.ext; unfold raw19377step3 raw19377step2; decide +kernel
      have hl : raw19377step2Labels = labelEmbedding9 ∘ raw19377step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19377step2 raw19377step2Labels raw19377step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw19378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw19378step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19378step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19378step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19378step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19378 raw19378Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw19378 raw19378Labels = mixedMoment B raw19378step0 raw19378step0Labels := by
      have hz : ∀ j, raw19378 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19378step0 = (fun i j => raw19378 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19378step0 raw19378; decide +kernel
      have hl : raw19378step0Labels = raw19378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19378 raw19378Labels permutation265 hz
    mixedMoment B raw19378step0 raw19378step0Labels = mixedMoment B raw19378step1 raw19378step1Labels := by
      have ha : raw19378step1 = (fun i j => raw19378step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19378step1 raw19378step0; decide +kernel
      have hl : raw19378step1Labels = raw19378step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19378step0 raw19378step0Labels permutation137 permutation4
    mixedMoment B raw19378step1 raw19378step1Labels = mixedMoment B raw19378step2 raw19378step2Labels := by
      have ha : raw19378step2 = -raw19378step1 := by apply Matrix.ext; change ∀ i j, raw19378step2 i j = -(raw19378step1 i j); unfold raw19378step2 raw19378step1; decide +kernel
      have hl : raw19378step2Labels = raw19378step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19378step2 raw19378step2Labels = mixedMoment B raw19378step3 raw19378step3Labels := by
      have ha : raw19378step3 = raw19378step2 := by apply Matrix.ext; unfold raw19378step3 raw19378step2; decide +kernel
      have hl : raw19378step2Labels = labelEmbedding7 ∘ raw19378step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19378step2 raw19378step2Labels raw19378step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw19379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19379step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19379 raw19379Labels = mixedMoment B node5398 node5398Labels := by
  calc
    mixedMoment B raw19379 raw19379Labels = mixedMoment B raw19379step0 raw19379step0Labels := by
      have ha : raw19379step0 = (fun i j => raw19379 (permutation294 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19379step0 raw19379; decide +kernel
      have hl : raw19379step0Labels = raw19379Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19379 raw19379Labels permutation294 permutation3
    mixedMoment B raw19379step0 raw19379step0Labels = mixedMoment B raw19379step1 raw19379step1Labels := by
      have ha : raw19379step1 = raw19379step0 := by apply Matrix.ext; unfold raw19379step1 raw19379step0; decide +kernel
      have hl : raw19379step0Labels = labelEmbedding6 ∘ raw19379step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19379step0 raw19379step0Labels raw19379step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5398 node5398Labels := by rfl

def raw19380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19380step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19380step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19380 raw19380Labels = mixedMoment B node5398 node5398Labels := by
  calc
    mixedMoment B raw19380 raw19380Labels = mixedMoment B raw19380step0 raw19380step0Labels := by
      have ha : raw19380step0 = (fun i j => raw19380 (permutation371 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19380step0 raw19380; decide +kernel
      have hl : raw19380step0Labels = raw19380Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19380 raw19380Labels permutation371 permutation3
    mixedMoment B raw19380step0 raw19380step0Labels = mixedMoment B raw19380step1 raw19380step1Labels := by
      have ha : raw19380step1 = raw19380step0 := by apply Matrix.ext; unfold raw19380step1 raw19380step0; decide +kernel
      have hl : raw19380step0Labels = labelEmbedding6 ∘ raw19380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19380step0 raw19380step0Labels raw19380step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5398 node5398Labels := by rfl

def raw19381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw19381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19381step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19381step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19381step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19381step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19381 raw19381Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw19381 raw19381Labels = mixedMoment B raw19381step0 raw19381step0Labels := by
      have hz : ∀ j, raw19381 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19381step0 = (fun i j => raw19381 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19381step0 raw19381; decide +kernel
      have hl : raw19381step0Labels = raw19381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19381 raw19381Labels permutation520 hz
    mixedMoment B raw19381step0 raw19381step0Labels = mixedMoment B raw19381step1 raw19381step1Labels := by
      have ha : raw19381step1 = (fun i j => raw19381step0 (permutation122 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19381step1 raw19381step0; decide +kernel
      have hl : raw19381step1Labels = raw19381step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19381step0 raw19381step0Labels permutation122 permutation3
    mixedMoment B raw19381step1 raw19381step1Labels = mixedMoment B raw19381step2 raw19381step2Labels := by
      have ha : raw19381step2 = -raw19381step1 := by apply Matrix.ext; change ∀ i j, raw19381step2 i j = -(raw19381step1 i j); unfold raw19381step2 raw19381step1; decide +kernel
      have hl : raw19381step2Labels = raw19381step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19381step2 raw19381step2Labels = mixedMoment B raw19381step3 raw19381step3Labels := by
      have ha : raw19381step3 = raw19381step2 := by apply Matrix.ext; unfold raw19381step3 raw19381step2; decide +kernel
      have hl : raw19381step2Labels = labelEmbedding6 ∘ raw19381step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19381step2 raw19381step2Labels raw19381step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw19382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw19382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19382step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19382step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19382 raw19382Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw19382 raw19382Labels = mixedMoment B raw19382step0 raw19382step0Labels := by
      have ha : raw19382step0 = (fun i j => raw19382 (permutation484 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19382step0 raw19382; decide +kernel
      have hl : raw19382step0Labels = raw19382Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19382 raw19382Labels permutation484 permutation5
    mixedMoment B raw19382step0 raw19382step0Labels = mixedMoment B raw19382step1 raw19382step1Labels := by
      have ha : raw19382step1 = raw19382step0 := by apply Matrix.ext; unfold raw19382step1 raw19382step0; decide +kernel
      have hl : raw19382step0Labels = labelEmbedding8 ∘ raw19382step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19382step0 raw19382step0Labels raw19382step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw19383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19383step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19383 raw19383Labels = mixedMoment B node5398 node5398Labels := by
  calc
    mixedMoment B raw19383 raw19383Labels = mixedMoment B raw19383step0 raw19383step0Labels := by
      have ha : raw19383step0 = (fun i j => raw19383 (permutation293 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19383step0 raw19383; decide +kernel
      have hl : raw19383step0Labels = raw19383Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19383 raw19383Labels permutation293 permutation3
    mixedMoment B raw19383step0 raw19383step0Labels = mixedMoment B raw19383step1 raw19383step1Labels := by
      have ha : raw19383step1 = raw19383step0 := by apply Matrix.ext; unfold raw19383step1 raw19383step0; decide +kernel
      have hl : raw19383step0Labels = labelEmbedding6 ∘ raw19383step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19383step0 raw19383step0Labels raw19383step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5398 node5398Labels := by rfl

def raw19384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19384step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19384 raw19384Labels = mixedMoment B node5398 node5398Labels := by
  calc
    mixedMoment B raw19384 raw19384Labels = mixedMoment B raw19384step0 raw19384step0Labels := by
      have ha : raw19384step0 = (fun i j => raw19384 (permutation370 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19384step0 raw19384; decide +kernel
      have hl : raw19384step0Labels = raw19384Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19384 raw19384Labels permutation370 permutation3
    mixedMoment B raw19384step0 raw19384step0Labels = mixedMoment B raw19384step1 raw19384step1Labels := by
      have ha : raw19384step1 = raw19384step0 := by apply Matrix.ext; unfold raw19384step1 raw19384step0; decide +kernel
      have hl : raw19384step0Labels = labelEmbedding6 ∘ raw19384step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19384step0 raw19384step0Labels raw19384step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5398 node5398Labels := by rfl

def raw19385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw19385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19385step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19385step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19385step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19385step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19385 raw19385Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw19385 raw19385Labels = mixedMoment B raw19385step0 raw19385step0Labels := by
      have hz : ∀ j, raw19385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19385step0 = (fun i j => raw19385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19385step0 raw19385; decide +kernel
      have hl : raw19385step0Labels = raw19385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19385 raw19385Labels permutation434 hz
    mixedMoment B raw19385step0 raw19385step0Labels = mixedMoment B raw19385step1 raw19385step1Labels := by
      have ha : raw19385step1 = (fun i j => raw19385step0 (permutation122 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19385step1 raw19385step0; decide +kernel
      have hl : raw19385step1Labels = raw19385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19385step0 raw19385step0Labels permutation122 permutation3
    mixedMoment B raw19385step1 raw19385step1Labels = mixedMoment B raw19385step2 raw19385step2Labels := by
      have ha : raw19385step2 = -raw19385step1 := by apply Matrix.ext; change ∀ i j, raw19385step2 i j = -(raw19385step1 i j); unfold raw19385step2 raw19385step1; decide +kernel
      have hl : raw19385step2Labels = raw19385step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19385step2 raw19385step2Labels = mixedMoment B raw19385step3 raw19385step3Labels := by
      have ha : raw19385step3 = raw19385step2 := by apply Matrix.ext; unfold raw19385step3 raw19385step2; decide +kernel
      have hl : raw19385step2Labels = labelEmbedding6 ∘ raw19385step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19385step2 raw19385step2Labels raw19385step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw19386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw19386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19386step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19386 raw19386Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw19386 raw19386Labels = mixedMoment B raw19386step0 raw19386step0Labels := by
      have ha : raw19386step0 = (fun i j => raw19386 (permutation553 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19386step0 raw19386; decide +kernel
      have hl : raw19386step0Labels = raw19386Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19386 raw19386Labels permutation553 permutation5
    mixedMoment B raw19386step0 raw19386step0Labels = mixedMoment B raw19386step1 raw19386step1Labels := by
      have ha : raw19386step1 = raw19386step0 := by apply Matrix.ext; unfold raw19386step1 raw19386step0; decide +kernel
      have hl : raw19386step0Labels = labelEmbedding8 ∘ raw19386step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19386step0 raw19386step0Labels raw19386step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw19387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19387step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19387 raw19387Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw19387 raw19387Labels = mixedMoment B raw19387step0 raw19387step0Labels := by
      have ha : raw19387step0 = (fun i j => raw19387 (permutation289 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19387step0 raw19387; decide +kernel
      have hl : raw19387step0Labels = raw19387Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19387 raw19387Labels permutation289 permutation3
    mixedMoment B raw19387step0 raw19387step0Labels = mixedMoment B raw19387step1 raw19387step1Labels := by
      have ha : raw19387step1 = raw19387step0 := by apply Matrix.ext; unfold raw19387step1 raw19387step0; decide +kernel
      have hl : raw19387step0Labels = labelEmbedding6 ∘ raw19387step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19387step0 raw19387step0Labels raw19387step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw19388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19388step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19388step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19388 raw19388Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw19388 raw19388Labels = mixedMoment B raw19388step0 raw19388step0Labels := by
      have ha : raw19388step0 = (fun i j => raw19388 (permutation367 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19388step0 raw19388; decide +kernel
      have hl : raw19388step0Labels = raw19388Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19388 raw19388Labels permutation367 permutation3
    mixedMoment B raw19388step0 raw19388step0Labels = mixedMoment B raw19388step1 raw19388step1Labels := by
      have ha : raw19388step1 = raw19388step0 := by apply Matrix.ext; unfold raw19388step1 raw19388step0; decide +kernel
      have hl : raw19388step0Labels = labelEmbedding6 ∘ raw19388step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19388step0 raw19388step0Labels raw19388step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw19389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw19389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw19389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19389 raw19389Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw19389 raw19389Labels = mixedMoment B raw19389step0 raw19389step0Labels := by
      have hz : ∀ j, raw19389 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19389step0 = (fun i j => raw19389 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19389step0 raw19389; decide +kernel
      have hl : raw19389step0Labels = raw19389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19389 raw19389Labels permutation520 hz
    mixedMoment B raw19389step0 raw19389step0Labels = mixedMoment B raw19389step1 raw19389step1Labels := by
      have ha : raw19389step1 = (fun i j => raw19389step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19389step1 raw19389step0; decide +kernel
      have hl : raw19389step1Labels = raw19389step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19389step0 raw19389step0Labels permutation149 permutation2
    mixedMoment B raw19389step1 raw19389step1Labels = mixedMoment B raw19389step2 raw19389step2Labels := by
      have ha : raw19389step2 = -raw19389step1 := by apply Matrix.ext; change ∀ i j, raw19389step2 i j = -(raw19389step1 i j); unfold raw19389step2 raw19389step1; decide +kernel
      have hl : raw19389step2Labels = raw19389step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw19390 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19390step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19390step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19390 raw19390Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19390 raw19390Labels = mixedMoment B raw19390step0 raw19390step0Labels := by
      have hz : ∀ j, raw19390 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw19390step0 = (fun i j => raw19390 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw19390step0 raw19390; decide +kernel
      have hl : raw19390step0Labels = raw19390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19390 raw19390Labels permutation152 hz
    mixedMoment B raw19390step0 raw19390step0Labels = mixedMoment B raw19390step1 raw19390step1Labels := by
      have hz : ∀ i, raw19390step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19390step1 = (fun i j => raw19390step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19390step1 raw19390step0; decide +kernel
      have hl : raw19390step1Labels = (fun j => raw19390step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19390step0 raw19390step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw19391 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19391step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw19391step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19391step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19391step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19391 raw19391Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19391 raw19391Labels = mixedMoment B raw19391step0 raw19391step0Labels := by
      have hz : ∀ j, raw19391 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw19391step0 = (fun i j => raw19391 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw19391step0 raw19391; decide +kernel
      have hl : raw19391step0Labels = raw19391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19391 raw19391Labels permutation152 hz
    mixedMoment B raw19391step0 raw19391step0Labels = mixedMoment B raw19391step1 raw19391step1Labels := by
      have hz : ∀ i, raw19391step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19391step1 = (fun i j => raw19391step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19391step1 raw19391step0; decide +kernel
      have hl : raw19391step1Labels = (fun j => raw19391step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19391step0 raw19391step0Labels permutation6 hz
    mixedMoment B raw19391step1 raw19391step1Labels = mixedMoment B raw19391step2 raw19391step2Labels := by
      have ha : raw19391step2 = (fun i j => raw19391step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19391step2 raw19391step1; decide +kernel
      have hl : raw19391step2Labels = raw19391step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19391step1 raw19391step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw19392 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw19392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19392step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19392step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw19392step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19392 raw19392Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw19392 raw19392Labels = mixedMoment B raw19392step0 raw19392step0Labels := by
      have hz : ∀ j, raw19392 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19392step0 = (fun i j => raw19392 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19392step0 raw19392; decide +kernel
      have hl : raw19392step0Labels = raw19392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19392 raw19392Labels permutation520 hz
    mixedMoment B raw19392step0 raw19392step0Labels = mixedMoment B raw19392step1 raw19392step1Labels := by
      have hz : ∀ j, raw19392step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw19392step1 = (fun i j => raw19392step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw19392step1 raw19392step0; decide +kernel
      have hl : raw19392step1Labels = raw19392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19392step0 raw19392step0Labels permutation32 hz
    mixedMoment B raw19392step1 raw19392step1Labels = mixedMoment B raw19392step2 raw19392step2Labels := by
      have hz : ∀ i, raw19392step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19392step2 = (fun i j => raw19392step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19392step2 raw19392step1; decide +kernel
      have hl : raw19392step2Labels = (fun j => raw19392step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19392step1 raw19392step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw19393 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw19393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19393step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19393step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw19393step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19393 raw19393Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw19393 raw19393Labels = mixedMoment B raw19393step0 raw19393step0Labels := by
      have hz : ∀ j, raw19393 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19393step0 = (fun i j => raw19393 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19393step0 raw19393; decide +kernel
      have hl : raw19393step0Labels = raw19393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19393 raw19393Labels permutation590 hz
    mixedMoment B raw19393step0 raw19393step0Labels = mixedMoment B raw19393step1 raw19393step1Labels := by
      have hz : ∀ j, raw19393step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw19393step1 = (fun i j => raw19393step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw19393step1 raw19393step0; decide +kernel
      have hl : raw19393step1Labels = raw19393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19393step0 raw19393step0Labels permutation32 hz
    mixedMoment B raw19393step1 raw19393step1Labels = mixedMoment B raw19393step2 raw19393step2Labels := by
      have hz : ∀ i, raw19393step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19393step2 = (fun i j => raw19393step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19393step2 raw19393step1; decide +kernel
      have hl : raw19393step2Labels = (fun j => raw19393step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19393step1 raw19393step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw19394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19394step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19394step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw19394step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19394step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19394step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19394 raw19394Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19394 raw19394Labels = mixedMoment B raw19394step0 raw19394step0Labels := by
      have hz : ∀ j, raw19394 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19394step0 = (fun i j => raw19394 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19394step0 raw19394; decide +kernel
      have hl : raw19394step0Labels = raw19394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19394 raw19394Labels permutation265 hz
    mixedMoment B raw19394step0 raw19394step0Labels = mixedMoment B raw19394step1 raw19394step1Labels := by
      have hz : ∀ i, raw19394step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19394step1 = (fun i j => raw19394step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19394step1 raw19394step0; decide +kernel
      have hl : raw19394step1Labels = (fun j => raw19394step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19394step0 raw19394step0Labels permutation6 hz
    mixedMoment B raw19394step1 raw19394step1Labels = mixedMoment B raw19394step2 raw19394step2Labels := by
      have ha : raw19394step2 = (fun i j => raw19394step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19394step2 raw19394step1; decide +kernel
      have hl : raw19394step2Labels = raw19394step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19394step1 raw19394step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw19395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw19395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19395step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19395step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw19395step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19395 raw19395Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw19395 raw19395Labels = mixedMoment B raw19395step0 raw19395step0Labels := by
      have hz : ∀ j, raw19395 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19395step0 = (fun i j => raw19395 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19395step0 raw19395; decide +kernel
      have hl : raw19395step0Labels = raw19395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19395 raw19395Labels permutation520 hz
    mixedMoment B raw19395step0 raw19395step0Labels = mixedMoment B raw19395step1 raw19395step1Labels := by
      have hz : ∀ j, raw19395step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19395step1 = (fun i j => raw19395step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19395step1 raw19395step0; decide +kernel
      have hl : raw19395step1Labels = raw19395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19395step0 raw19395step0Labels permutation56 hz
    mixedMoment B raw19395step1 raw19395step1Labels = mixedMoment B raw19395step2 raw19395step2Labels := by
      have hz : ∀ i, raw19395step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19395step2 = (fun i j => raw19395step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19395step2 raw19395step1; decide +kernel
      have hl : raw19395step2Labels = (fun j => raw19395step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19395step1 raw19395step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw19396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw19396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19396step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19396step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw19396step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19396 raw19396Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw19396 raw19396Labels = mixedMoment B raw19396step0 raw19396step0Labels := by
      have hz : ∀ j, raw19396 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19396step0 = (fun i j => raw19396 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19396step0 raw19396; decide +kernel
      have hl : raw19396step0Labels = raw19396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19396 raw19396Labels permutation590 hz
    mixedMoment B raw19396step0 raw19396step0Labels = mixedMoment B raw19396step1 raw19396step1Labels := by
      have hz : ∀ j, raw19396step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19396step1 = (fun i j => raw19396step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19396step1 raw19396step0; decide +kernel
      have hl : raw19396step1Labels = raw19396step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19396step0 raw19396step0Labels permutation56 hz
    mixedMoment B raw19396step1 raw19396step1Labels = mixedMoment B raw19396step2 raw19396step2Labels := by
      have hz : ∀ i, raw19396step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19396step2 = (fun i j => raw19396step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19396step2 raw19396step1; decide +kernel
      have hl : raw19396step2Labels = (fun j => raw19396step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19396step1 raw19396step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw19397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19397step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw19397step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19397step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19397step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19397 raw19397Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19397 raw19397Labels = mixedMoment B raw19397step0 raw19397step0Labels := by
      have hz : ∀ i, raw19397 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19397step0 = (fun i j => raw19397 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19397step0 raw19397; decide +kernel
      have hl : raw19397step0Labels = (fun j => raw19397Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19397 raw19397Labels permutation6 hz
    mixedMoment B raw19397step0 raw19397step0Labels = mixedMoment B raw19397step1 raw19397step1Labels := by
      have ha : raw19397step1 = (fun i j => raw19397step0 (permutation268 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19397step1 raw19397step0; decide +kernel
      have hl : raw19397step1Labels = raw19397step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19397step0 raw19397step0Labels permutation268 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw19398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19398step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw19398step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19398step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19398step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19398 raw19398Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19398 raw19398Labels = mixedMoment B raw19398step0 raw19398step0Labels := by
      have hz : ∀ i, raw19398 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19398step0 = (fun i j => raw19398 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19398step0 raw19398; decide +kernel
      have hl : raw19398step0Labels = (fun j => raw19398Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19398 raw19398Labels permutation6 hz
    mixedMoment B raw19398step0 raw19398step0Labels = mixedMoment B raw19398step1 raw19398step1Labels := by
      have ha : raw19398step1 = (fun i j => raw19398step0 (permutation349 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19398step1 raw19398step0; decide +kernel
      have hl : raw19398step1Labels = raw19398step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19398step0 raw19398step0Labels permutation349 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw19399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw19399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19399step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw19399step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19399step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw19399step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19399step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19399step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19399 raw19399Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19399 raw19399Labels = mixedMoment B raw19399step0 raw19399step0Labels := by
      have hz : ∀ j, raw19399 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19399step0 = (fun i j => raw19399 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19399step0 raw19399; decide +kernel
      have hl : raw19399step0Labels = raw19399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19399 raw19399Labels permutation520 hz
    mixedMoment B raw19399step0 raw19399step0Labels = mixedMoment B raw19399step1 raw19399step1Labels := by
      have hz : ∀ i, raw19399step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19399step1 = (fun i j => raw19399step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19399step1 raw19399step0; decide +kernel
      have hl : raw19399step1Labels = (fun j => raw19399step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19399step0 raw19399step0Labels permutation6 hz
    mixedMoment B raw19399step1 raw19399step1Labels = mixedMoment B raw19399step2 raw19399step2Labels := by
      have ha : raw19399step2 = (fun i j => raw19399step1 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19399step2 raw19399step1; decide +kernel
      have hl : raw19399step2Labels = raw19399step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19399step1 raw19399step1Labels permutation122 permutation0
    mixedMoment B raw19399step2 raw19399step2Labels = mixedMoment B raw19399step3 raw19399step3Labels := by
      have ha : raw19399step3 = -raw19399step2 := by apply Matrix.ext; change ∀ i j, raw19399step3 i j = -(raw19399step2 i j); unfold raw19399step3 raw19399step2; decide +kernel
      have hl : raw19399step3Labels = raw19399step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw19400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw19400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19400step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw19400step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19400step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw19400step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19400step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19400step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19400 raw19400Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19400 raw19400Labels = mixedMoment B raw19400step0 raw19400step0Labels := by
      have hz : ∀ j, raw19400 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19400step0 = (fun i j => raw19400 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19400step0 raw19400; decide +kernel
      have hl : raw19400step0Labels = raw19400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19400 raw19400Labels permutation590 hz
    mixedMoment B raw19400step0 raw19400step0Labels = mixedMoment B raw19400step1 raw19400step1Labels := by
      have hz : ∀ i, raw19400step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19400step1 = (fun i j => raw19400step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19400step1 raw19400step0; decide +kernel
      have hl : raw19400step1Labels = (fun j => raw19400step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19400step0 raw19400step0Labels permutation6 hz
    mixedMoment B raw19400step1 raw19400step1Labels = mixedMoment B raw19400step2 raw19400step2Labels := by
      have ha : raw19400step2 = (fun i j => raw19400step1 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19400step2 raw19400step1; decide +kernel
      have hl : raw19400step2Labels = raw19400step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19400step1 raw19400step1Labels permutation122 permutation0
    mixedMoment B raw19400step2 raw19400step2Labels = mixedMoment B raw19400step3 raw19400step3Labels := by
      have ha : raw19400step3 = -raw19400step2 := by apply Matrix.ext; change ∀ i j, raw19400step3 i j = -(raw19400step2 i j); unfold raw19400step3 raw19400step2; decide +kernel
      have hl : raw19400step3Labels = raw19400step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw19401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19401step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw19401step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19401step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19401step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19401 raw19401Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19401 raw19401Labels = mixedMoment B raw19401step0 raw19401step0Labels := by
      have hz : ∀ i, raw19401 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19401step0 = (fun i j => raw19401 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19401step0 raw19401; decide +kernel
      have hl : raw19401step0Labels = (fun j => raw19401Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19401 raw19401Labels permutation6 hz
    mixedMoment B raw19401step0 raw19401step0Labels = mixedMoment B raw19401step1 raw19401step1Labels := by
      have ha : raw19401step1 = (fun i j => raw19401step0 (permutation266 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19401step1 raw19401step0; decide +kernel
      have hl : raw19401step1Labels = raw19401step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19401step0 raw19401step0Labels permutation266 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw19402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw19402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19402step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw19402step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19402step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19402step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19402 raw19402Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19402 raw19402Labels = mixedMoment B raw19402step0 raw19402step0Labels := by
      have hz : ∀ i, raw19402 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19402step0 = (fun i j => raw19402 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19402step0 raw19402; decide +kernel
      have hl : raw19402step0Labels = (fun j => raw19402Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19402 raw19402Labels permutation6 hz
    mixedMoment B raw19402step0 raw19402step0Labels = mixedMoment B raw19402step1 raw19402step1Labels := by
      have ha : raw19402step1 = (fun i j => raw19402step0 (permutation347 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19402step1 raw19402step0; decide +kernel
      have hl : raw19402step1Labels = raw19402step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19402step0 raw19402step0Labels permutation347 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw19403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw19403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw19403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19403step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw19403step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19403step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw19403step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19403step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19403step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19403 raw19403Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19403 raw19403Labels = mixedMoment B raw19403step0 raw19403step0Labels := by
      have hz : ∀ j, raw19403 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19403step0 = (fun i j => raw19403 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19403step0 raw19403; decide +kernel
      have hl : raw19403step0Labels = raw19403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19403 raw19403Labels permutation590 hz
    mixedMoment B raw19403step0 raw19403step0Labels = mixedMoment B raw19403step1 raw19403step1Labels := by
      have hz : ∀ i, raw19403step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19403step1 = (fun i j => raw19403step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19403step1 raw19403step0; decide +kernel
      have hl : raw19403step1Labels = (fun j => raw19403step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19403step0 raw19403step0Labels permutation6 hz
    mixedMoment B raw19403step1 raw19403step1Labels = mixedMoment B raw19403step2 raw19403step2Labels := by
      have ha : raw19403step2 = (fun i j => raw19403step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19403step2 raw19403step1; decide +kernel
      have hl : raw19403step2Labels = raw19403step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19403step1 raw19403step1Labels permutation146 permutation0
    mixedMoment B raw19403step2 raw19403step2Labels = mixedMoment B raw19403step3 raw19403step3Labels := by
      have ha : raw19403step3 = -raw19403step2 := by apply Matrix.ext; change ∀ i j, raw19403step3 i j = -(raw19403step2 i j); unfold raw19403step3 raw19403step2; decide +kernel
      have hl : raw19403step3Labels = raw19403step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw19404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw19404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19404step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19404step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19404step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19404step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19404 raw19404Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19404 raw19404Labels = mixedMoment B raw19404step0 raw19404step0Labels := by
      have hz : ∀ i, raw19404 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19404step0 = (fun i j => raw19404 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19404step0 raw19404; decide +kernel
      have hl : raw19404step0Labels = (fun j => raw19404Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19404 raw19404Labels permutation6 hz
    mixedMoment B raw19404step0 raw19404step0Labels = mixedMoment B raw19404step1 raw19404step1Labels := by
      have ha : raw19404step1 = (fun i j => raw19404step0 (permutation265 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19404step1 raw19404step0; decide +kernel
      have hl : raw19404step1Labels = raw19404step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19404step0 raw19404step0Labels permutation265 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw19405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw19405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19405step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw19405step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19405step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19405step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19405 raw19405Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw19405 raw19405Labels = mixedMoment B raw19405step0 raw19405step0Labels := by
      have hz : ∀ i, raw19405 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19405step0 = (fun i j => raw19405 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19405step0 raw19405; decide +kernel
      have hl : raw19405step0Labels = (fun j => raw19405Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19405 raw19405Labels permutation6 hz
    mixedMoment B raw19405step0 raw19405step0Labels = mixedMoment B raw19405step1 raw19405step1Labels := by
      have ha : raw19405step1 = (fun i j => raw19405step0 (permutation346 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19405step1 raw19405step0; decide +kernel
      have hl : raw19405step1Labels = raw19405step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19405step0 raw19405step0Labels permutation346 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw19406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw19406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw19406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19406step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw19406step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19406step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw19406step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19406step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19406step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19406 raw19406Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19406 raw19406Labels = mixedMoment B raw19406step0 raw19406step0Labels := by
      have hz : ∀ j, raw19406 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19406step0 = (fun i j => raw19406 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19406step0 raw19406; decide +kernel
      have hl : raw19406step0Labels = raw19406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19406 raw19406Labels permutation520 hz
    mixedMoment B raw19406step0 raw19406step0Labels = mixedMoment B raw19406step1 raw19406step1Labels := by
      have hz : ∀ i, raw19406step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw19406step1 = (fun i j => raw19406step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw19406step1 raw19406step0; decide +kernel
      have hl : raw19406step1Labels = (fun j => raw19406step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19406step0 raw19406step0Labels permutation6 hz
    mixedMoment B raw19406step1 raw19406step1Labels = mixedMoment B raw19406step2 raw19406step2Labels := by
      have ha : raw19406step2 = (fun i j => raw19406step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19406step2 raw19406step1; decide +kernel
      have hl : raw19406step2Labels = raw19406step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19406step1 raw19406step1Labels permutation146 permutation0
    mixedMoment B raw19406step2 raw19406step2Labels = mixedMoment B raw19406step3 raw19406step3Labels := by
      have ha : raw19406step3 = -raw19406step2 := by apply Matrix.ext; change ∀ i j, raw19406step3 i j = -(raw19406step2 i j); unfold raw19406step3 raw19406step2; decide +kernel
      have hl : raw19406step3Labels = raw19406step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw19407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19407step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw19407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19407 raw19407Labels = mixedMoment B node617 node617Labels := by
  calc
    mixedMoment B raw19407 raw19407Labels = mixedMoment B raw19407step0 raw19407step0Labels := by
      have hz : ∀ j, raw19407 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19407step0 = (fun i j => raw19407 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19407step0 raw19407; decide +kernel
      have hl : raw19407step0Labels = raw19407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19407 raw19407Labels permutation434 hz
    mixedMoment B raw19407step0 raw19407step0Labels = mixedMoment B raw19407step1 raw19407step1Labels := by
      have hz : ∀ j, raw19407step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19407step1 = (fun i j => raw19407step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19407step1 raw19407step0; decide +kernel
      have hl : raw19407step1Labels = raw19407step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19407step0 raw19407step0Labels permutation80 hz
    mixedMoment B raw19407step1 raw19407step1Labels = mixedMoment B raw19407step2 raw19407step2Labels := by
      have hz : ∀ j, raw19407step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19407step2 = (fun i j => raw19407step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19407step2 raw19407step1; decide +kernel
      have hl : raw19407step2Labels = raw19407step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19407step1 raw19407step1Labels permutation14 hz
    _ = mixedMoment B node617 node617Labels := by rfl

def raw19408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19408 raw19408Labels = mixedMoment B node936 node936Labels := by
  calc
    mixedMoment B raw19408 raw19408Labels = mixedMoment B raw19408step0 raw19408step0Labels := by
      have hz : ∀ j, raw19408 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19408step0 = (fun i j => raw19408 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19408step0 raw19408; decide +kernel
      have hl : raw19408step0Labels = raw19408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19408 raw19408Labels permutation434 hz
    mixedMoment B raw19408step0 raw19408step0Labels = mixedMoment B raw19408step1 raw19408step1Labels := by
      have hz : ∀ j, raw19408step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19408step1 = (fun i j => raw19408step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19408step1 raw19408step0; decide +kernel
      have hl : raw19408step1Labels = raw19408step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19408step0 raw19408step0Labels permutation80 hz
    _ = mixedMoment B node936 node936Labels := by rfl

def raw19409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19409 raw19409Labels = mixedMoment B node936 node936Labels := by
  calc
    mixedMoment B raw19409 raw19409Labels = mixedMoment B raw19409step0 raw19409step0Labels := by
      have hz : ∀ j, raw19409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19409step0 = (fun i j => raw19409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19409step0 raw19409; decide +kernel
      have hl : raw19409step0Labels = raw19409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19409 raw19409Labels permutation434 hz
    mixedMoment B raw19409step0 raw19409step0Labels = mixedMoment B raw19409step1 raw19409step1Labels := by
      have hz : ∀ j, raw19409step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19409step1 = (fun i j => raw19409step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19409step1 raw19409step0; decide +kernel
      have hl : raw19409step1Labels = raw19409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19409step0 raw19409step0Labels permutation56 hz
    _ = mixedMoment B node936 node936Labels := by rfl

def raw19410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw19410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19410 raw19410Labels = mixedMoment B node936 node936Labels := by
  calc
    mixedMoment B raw19410 raw19410Labels = mixedMoment B raw19410step0 raw19410step0Labels := by
      have hz : ∀ j, raw19410 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19410step0 = (fun i j => raw19410 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19410step0 raw19410; decide +kernel
      have hl : raw19410step0Labels = raw19410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19410 raw19410Labels permutation346 hz
    mixedMoment B raw19410step0 raw19410step0Labels = mixedMoment B raw19410step1 raw19410step1Labels := by
      have hz : ∀ j, raw19410step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19410step1 = (fun i j => raw19410step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19410step1 raw19410step0; decide +kernel
      have hl : raw19410step1Labels = raw19410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19410step0 raw19410step0Labels permutation56 hz
    _ = mixedMoment B node936 node936Labels := by rfl

def raw19411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw19411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw19411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw19411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19411step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw19411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19411 raw19411Labels = mixedMoment B node1064 node1064Labels := by
  calc
    mixedMoment B raw19411 raw19411Labels = mixedMoment B raw19411step0 raw19411step0Labels := by
      have hz : ∀ j, raw19411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19411step0 = (fun i j => raw19411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19411step0 raw19411; decide +kernel
      have hl : raw19411step0Labels = raw19411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19411 raw19411Labels permutation434 hz
    mixedMoment B raw19411step0 raw19411step0Labels = mixedMoment B raw19411step1 raw19411step1Labels := by
      have hz : ∀ j, raw19411step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19411step1 = (fun i j => raw19411step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19411step1 raw19411step0; decide +kernel
      have hl : raw19411step1Labels = raw19411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19411step0 raw19411step0Labels permutation80 hz
    mixedMoment B raw19411step1 raw19411step1Labels = mixedMoment B raw19411step2 raw19411step2Labels := by
      have hz : ∀ j, raw19411step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19411step2 = (fun i j => raw19411step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19411step2 raw19411step1; decide +kernel
      have hl : raw19411step2Labels = raw19411step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19411step1 raw19411step1Labels permutation14 hz
    _ = mixedMoment B node1064 node1064Labels := by rfl

def raw19412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw19412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw19412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw19412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19412step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw19412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19412 raw19412Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw19412 raw19412Labels = mixedMoment B raw19412step0 raw19412step0Labels := by
      have hz : ∀ j, raw19412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19412step0 = (fun i j => raw19412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19412step0 raw19412; decide +kernel
      have hl : raw19412step0Labels = raw19412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19412 raw19412Labels permutation434 hz
    mixedMoment B raw19412step0 raw19412step0Labels = mixedMoment B raw19412step1 raw19412step1Labels := by
      have hz : ∀ j, raw19412step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19412step1 = (fun i j => raw19412step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19412step1 raw19412step0; decide +kernel
      have hl : raw19412step1Labels = raw19412step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19412step0 raw19412step0Labels permutation80 hz
    mixedMoment B raw19412step1 raw19412step1Labels = mixedMoment B raw19412step2 raw19412step2Labels := by
      have hz : ∀ j, raw19412step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19412step2 = (fun i j => raw19412step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19412step2 raw19412step1; decide +kernel
      have hl : raw19412step2Labels = raw19412step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19412step1 raw19412step1Labels permutation14 hz
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw19413 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw19413Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19413step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw19413step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19413step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]
def raw19413step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19413step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw19413step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19413step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw19413step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19413 raw19413Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw19413 raw19413Labels = mixedMoment B raw19413step0 raw19413step0Labels := by
      have hz : ∀ j, raw19413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19413step0 = (fun i j => raw19413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19413step0 raw19413; decide +kernel
      have hl : raw19413step0Labels = raw19413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413 raw19413Labels permutation434 hz
    mixedMoment B raw19413step0 raw19413step0Labels = mixedMoment B raw19413step1 raw19413step1Labels := by
      have hz : ∀ j, raw19413step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19413step1 = (fun i j => raw19413step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19413step1 raw19413step0; decide +kernel
      have hl : raw19413step1Labels = raw19413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413step0 raw19413step0Labels permutation80 hz
    mixedMoment B raw19413step1 raw19413step1Labels = mixedMoment B raw19413step2 raw19413step2Labels := by
      have hz : ∀ j, raw19413step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19413step2 = (fun i j => raw19413step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19413step2 raw19413step1; decide +kernel
      have hl : raw19413step2Labels = raw19413step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19413step1 raw19413step1Labels permutation14 hz
    mixedMoment B raw19413step2 raw19413step2Labels = mixedMoment B raw19413step3 raw19413step3Labels := by
      have ha : raw19413step3 = (fun i j => raw19413step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19413step3 raw19413step2; decide +kernel
      have hl : raw19413step3Labels = raw19413step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19413step2 raw19413step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw19414 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19414step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-3, -1, 4]]
def raw19414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19414step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw19414step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19414 raw19414Labels = mixedMoment B node1757 node1757Labels := by
  calc
    mixedMoment B raw19414 raw19414Labels = mixedMoment B raw19414step0 raw19414step0Labels := by
      have hz : ∀ j, raw19414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19414step0 = (fun i j => raw19414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19414step0 raw19414; decide +kernel
      have hl : raw19414step0Labels = raw19414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19414 raw19414Labels permutation434 hz
    mixedMoment B raw19414step0 raw19414step0Labels = mixedMoment B raw19414step1 raw19414step1Labels := by
      have hz : ∀ j, raw19414step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19414step1 = (fun i j => raw19414step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19414step1 raw19414step0; decide +kernel
      have hl : raw19414step1Labels = raw19414step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19414step0 raw19414step0Labels permutation80 hz
    mixedMoment B raw19414step1 raw19414step1Labels = mixedMoment B raw19414step2 raw19414step2Labels := by
      have hz : ∀ j, raw19414step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19414step2 = (fun i j => raw19414step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19414step2 raw19414step1; decide +kernel
      have hl : raw19414step2Labels = raw19414step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19414step1 raw19414step1Labels permutation14 hz
    mixedMoment B raw19414step2 raw19414step2Labels = mixedMoment B raw19414step3 raw19414step3Labels := by
      have ha : raw19414step3 = (fun i j => raw19414step2 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19414step3 raw19414step2; decide +kernel
      have hl : raw19414step3Labels = raw19414step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19414step2 raw19414step2Labels permutation6 permutation2
    _ = mixedMoment B node1757 node1757Labels := by rfl

def raw19415 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw19415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19415 raw19415Labels = mixedMoment B node1629 node1629Labels := by
  calc
    mixedMoment B raw19415 raw19415Labels = mixedMoment B raw19415step0 raw19415step0Labels := by
      have hz : ∀ j, raw19415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19415step0 = (fun i j => raw19415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19415step0 raw19415; decide +kernel
      have hl : raw19415step0Labels = raw19415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19415 raw19415Labels permutation434 hz
    mixedMoment B raw19415step0 raw19415step0Labels = mixedMoment B raw19415step1 raw19415step1Labels := by
      have hz : ∀ j, raw19415step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19415step1 = (fun i j => raw19415step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19415step1 raw19415step0; decide +kernel
      have hl : raw19415step1Labels = raw19415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19415step0 raw19415step0Labels permutation80 hz
    mixedMoment B raw19415step1 raw19415step1Labels = mixedMoment B raw19415step2 raw19415step2Labels := by
      have ha : raw19415step2 = (fun i j => raw19415step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19415step2 raw19415step1; decide +kernel
      have hl : raw19415step2Labels = raw19415step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19415step1 raw19415step1Labels permutation29 permutation2
    _ = mixedMoment B node1629 node1629Labels := by rfl

def raw19416 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw19416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19416 raw19416Labels = mixedMoment B node1629 node1629Labels := by
  calc
    mixedMoment B raw19416 raw19416Labels = mixedMoment B raw19416step0 raw19416step0Labels := by
      have hz : ∀ j, raw19416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19416step0 = (fun i j => raw19416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19416step0 raw19416; decide +kernel
      have hl : raw19416step0Labels = raw19416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19416 raw19416Labels permutation434 hz
    mixedMoment B raw19416step0 raw19416step0Labels = mixedMoment B raw19416step1 raw19416step1Labels := by
      have hz : ∀ j, raw19416step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19416step1 = (fun i j => raw19416step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19416step1 raw19416step0; decide +kernel
      have hl : raw19416step1Labels = raw19416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19416step0 raw19416step0Labels permutation56 hz
    mixedMoment B raw19416step1 raw19416step1Labels = mixedMoment B raw19416step2 raw19416step2Labels := by
      have ha : raw19416step2 = (fun i j => raw19416step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19416step2 raw19416step1; decide +kernel
      have hl : raw19416step2Labels = raw19416step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19416step1 raw19416step1Labels permutation29 permutation2
    _ = mixedMoment B node1629 node1629Labels := by rfl

def raw19417 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw19417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19417 raw19417Labels = mixedMoment B node1629 node1629Labels := by
  calc
    mixedMoment B raw19417 raw19417Labels = mixedMoment B raw19417step0 raw19417step0Labels := by
      have hz : ∀ j, raw19417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19417step0 = (fun i j => raw19417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19417step0 raw19417; decide +kernel
      have hl : raw19417step0Labels = raw19417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19417 raw19417Labels permutation346 hz
    mixedMoment B raw19417step0 raw19417step0Labels = mixedMoment B raw19417step1 raw19417step1Labels := by
      have hz : ∀ j, raw19417step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19417step1 = (fun i j => raw19417step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19417step1 raw19417step0; decide +kernel
      have hl : raw19417step1Labels = raw19417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19417step0 raw19417step0Labels permutation56 hz
    mixedMoment B raw19417step1 raw19417step1Labels = mixedMoment B raw19417step2 raw19417step2Labels := by
      have ha : raw19417step2 = (fun i j => raw19417step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19417step2 raw19417step1; decide +kernel
      have hl : raw19417step2Labels = raw19417step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19417step1 raw19417step1Labels permutation29 permutation2
    _ = mixedMoment B node1629 node1629Labels := by rfl

def raw19418 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19418step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19418step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19418step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19418 raw19418Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19418 raw19418Labels = mixedMoment B raw19418step0 raw19418step0Labels := by
      have hz : ∀ j, raw19418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19418step0 = (fun i j => raw19418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19418step0 raw19418; decide +kernel
      have hl : raw19418step0Labels = raw19418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19418 raw19418Labels permutation434 hz
    mixedMoment B raw19418step0 raw19418step0Labels = mixedMoment B raw19418step1 raw19418step1Labels := by
      have hz : ∀ j, raw19418step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19418step1 = (fun i j => raw19418step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19418step1 raw19418step0; decide +kernel
      have hl : raw19418step1Labels = raw19418step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19418step0 raw19418step0Labels permutation80 hz
    mixedMoment B raw19418step1 raw19418step1Labels = mixedMoment B raw19418step2 raw19418step2Labels := by
      have hz : ∀ j, raw19418step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19418step2 = (fun i j => raw19418step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19418step2 raw19418step1; decide +kernel
      have hl : raw19418step2Labels = raw19418step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19418step1 raw19418step1Labels permutation14 hz
    mixedMoment B raw19418step2 raw19418step2Labels = mixedMoment B raw19418step3 raw19418step3Labels := by
      have ha : raw19418step3 = (fun i j => raw19418step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19418step3 raw19418step2; decide +kernel
      have hl : raw19418step3Labels = raw19418step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19418step2 raw19418step2Labels permutation7 permutation2
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw19419 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 0, 4]]
def raw19419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-4, 0, 4]]
def raw19419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-4, 0, 4]]
def raw19419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19419step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-4, 0, 4]]
def raw19419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19419step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -2, 0], ![2, 2, -4]]
def raw19419step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19419 raw19419Labels = mixedMoment B node862 node862Labels := by
  calc
    mixedMoment B raw19419 raw19419Labels = mixedMoment B raw19419step0 raw19419step0Labels := by
      have hz : ∀ j, raw19419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19419step0 = (fun i j => raw19419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19419step0 raw19419; decide +kernel
      have hl : raw19419step0Labels = raw19419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19419 raw19419Labels permutation434 hz
    mixedMoment B raw19419step0 raw19419step0Labels = mixedMoment B raw19419step1 raw19419step1Labels := by
      have hz : ∀ j, raw19419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19419step1 = (fun i j => raw19419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19419step1 raw19419step0; decide +kernel
      have hl : raw19419step1Labels = raw19419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19419step0 raw19419step0Labels permutation80 hz
    mixedMoment B raw19419step1 raw19419step1Labels = mixedMoment B raw19419step2 raw19419step2Labels := by
      have hz : ∀ j, raw19419step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19419step2 = (fun i j => raw19419step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19419step2 raw19419step1; decide +kernel
      have hl : raw19419step2Labels = raw19419step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19419step1 raw19419step1Labels permutation14 hz
    mixedMoment B raw19419step2 raw19419step2Labels = mixedMoment B raw19419step3 raw19419step3Labels := by
      have ha : raw19419step3 = (fun i j => raw19419step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19419step3 raw19419step2; decide +kernel
      have hl : raw19419step3Labels = raw19419step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19419step2 raw19419step2Labels permutation7 permutation2
    _ = mixedMoment B node862 node862Labels := by rfl

def raw19420 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-4, 4]]
def raw19420Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19420step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![0, 0], ![-4, 4]]
def raw19420step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19420step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![-4, 4]]
def raw19420step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19420step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![-4, 4]]
def raw19420step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19420step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![4, -4], ![-4, 4]]
def raw19420step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19420step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]
def raw19420step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19420 raw19420Labels = mixedMoment B node4072 node4072Labels := by
  calc
    mixedMoment B raw19420 raw19420Labels = mixedMoment B raw19420step0 raw19420step0Labels := by
      have hz : ∀ j, raw19420 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19420step0 = (fun i j => raw19420 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19420step0 raw19420; decide +kernel
      have hl : raw19420step0Labels = raw19420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19420 raw19420Labels permutation520 hz
    mixedMoment B raw19420step0 raw19420step0Labels = mixedMoment B raw19420step1 raw19420step1Labels := by
      have hz : ∀ j, raw19420step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19420step1 = (fun i j => raw19420step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19420step1 raw19420step0; decide +kernel
      have hl : raw19420step1Labels = raw19420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19420step0 raw19420step0Labels permutation104 hz
    mixedMoment B raw19420step1 raw19420step1Labels = mixedMoment B raw19420step2 raw19420step2Labels := by
      have hz : ∀ j, raw19420step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19420step2 = (fun i j => raw19420step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19420step2 raw19420step1; decide +kernel
      have hl : raw19420step2Labels = raw19420step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19420step1 raw19420step1Labels permutation20 hz
    mixedMoment B raw19420step2 raw19420step2Labels = mixedMoment B raw19420step3 raw19420step3Labels := by
      have hz : ∀ j, raw19420step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19420step3 = (fun i j => raw19420step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19420step3 raw19420step2; decide +kernel
      have hl : raw19420step3Labels = raw19420step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19420step2 raw19420step2Labels permutation4 hz
    mixedMoment B raw19420step3 raw19420step3Labels = mixedMoment B raw19420step4 raw19420step4Labels := by
      have ha : raw19420step4 = (fun i j => raw19420step3 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19420step4 raw19420step3; decide +kernel
      have hl : raw19420step4Labels = raw19420step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19420step3 raw19420step3Labels permutation1 permutation0
    _ = mixedMoment B node4072 node4072Labels := by rfl

def raw19421 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -3, 4], ![-2, 2, 0]]
def raw19421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 3, -4], ![2, -2, 0]]
def raw19421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19421 raw19421Labels = mixedMoment B node854 node854Labels := by
  calc
    mixedMoment B raw19421 raw19421Labels = mixedMoment B raw19421step0 raw19421step0Labels := by
      have hz : ∀ j, raw19421 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19421step0 = (fun i j => raw19421 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19421step0 raw19421; decide +kernel
      have hl : raw19421step0Labels = raw19421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19421 raw19421Labels permutation434 hz
    mixedMoment B raw19421step0 raw19421step0Labels = mixedMoment B raw19421step1 raw19421step1Labels := by
      have hz : ∀ j, raw19421step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19421step1 = (fun i j => raw19421step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19421step1 raw19421step0; decide +kernel
      have hl : raw19421step1Labels = raw19421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19421step0 raw19421step0Labels permutation80 hz
    mixedMoment B raw19421step1 raw19421step1Labels = mixedMoment B raw19421step2 raw19421step2Labels := by
      have ha : raw19421step2 = (fun i j => raw19421step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19421step2 raw19421step1; decide +kernel
      have hl : raw19421step2Labels = raw19421step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19421step1 raw19421step1Labels permutation9 permutation4
    mixedMoment B raw19421step2 raw19421step2Labels = mixedMoment B raw19421step3 raw19421step3Labels := by
      have ha : raw19421step3 = -raw19421step2 := by apply Matrix.ext; change ∀ i j, raw19421step3 i j = -(raw19421step2 i j); unfold raw19421step3 raw19421step2; decide +kernel
      have hl : raw19421step3Labels = raw19421step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node854 node854Labels := by rfl

def raw19422 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19422step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -3, 4], ![-2, 2, 0]]
def raw19422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19422step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 3, -4], ![2, -2, 0]]
def raw19422step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19422 raw19422Labels = mixedMoment B node854 node854Labels := by
  calc
    mixedMoment B raw19422 raw19422Labels = mixedMoment B raw19422step0 raw19422step0Labels := by
      have hz : ∀ j, raw19422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19422step0 = (fun i j => raw19422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19422step0 raw19422; decide +kernel
      have hl : raw19422step0Labels = raw19422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19422 raw19422Labels permutation434 hz
    mixedMoment B raw19422step0 raw19422step0Labels = mixedMoment B raw19422step1 raw19422step1Labels := by
      have hz : ∀ j, raw19422step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19422step1 = (fun i j => raw19422step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19422step1 raw19422step0; decide +kernel
      have hl : raw19422step1Labels = raw19422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19422step0 raw19422step0Labels permutation56 hz
    mixedMoment B raw19422step1 raw19422step1Labels = mixedMoment B raw19422step2 raw19422step2Labels := by
      have ha : raw19422step2 = (fun i j => raw19422step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19422step2 raw19422step1; decide +kernel
      have hl : raw19422step2Labels = raw19422step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19422step1 raw19422step1Labels permutation9 permutation4
    mixedMoment B raw19422step2 raw19422step2Labels = mixedMoment B raw19422step3 raw19422step3Labels := by
      have ha : raw19422step3 = -raw19422step2 := by apply Matrix.ext; change ∀ i j, raw19422step3 i j = -(raw19422step2 i j); unfold raw19422step3 raw19422step2; decide +kernel
      have hl : raw19422step3Labels = raw19422step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node854 node854Labels := by rfl

def raw19423 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19423step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![-3, -1, 4]]
def raw19423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19423step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -3, 4], ![-2, 2, 0]]
def raw19423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19423step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 3, -4], ![2, -2, 0]]
def raw19423step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19423 raw19423Labels = mixedMoment B node854 node854Labels := by
  calc
    mixedMoment B raw19423 raw19423Labels = mixedMoment B raw19423step0 raw19423step0Labels := by
      have hz : ∀ j, raw19423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19423step0 = (fun i j => raw19423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19423step0 raw19423; decide +kernel
      have hl : raw19423step0Labels = raw19423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19423 raw19423Labels permutation346 hz
    mixedMoment B raw19423step0 raw19423step0Labels = mixedMoment B raw19423step1 raw19423step1Labels := by
      have hz : ∀ j, raw19423step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19423step1 = (fun i j => raw19423step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19423step1 raw19423step0; decide +kernel
      have hl : raw19423step1Labels = raw19423step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19423step0 raw19423step0Labels permutation56 hz
    mixedMoment B raw19423step1 raw19423step1Labels = mixedMoment B raw19423step2 raw19423step2Labels := by
      have ha : raw19423step2 = (fun i j => raw19423step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19423step2 raw19423step1; decide +kernel
      have hl : raw19423step2Labels = raw19423step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19423step1 raw19423step1Labels permutation9 permutation4
    mixedMoment B raw19423step2 raw19423step2Labels = mixedMoment B raw19423step3 raw19423step3Labels := by
      have ha : raw19423step3 = -raw19423step2 := by apply Matrix.ext; change ∀ i j, raw19423step3 i j = -(raw19423step2 i j); unfold raw19423step3 raw19423step2; decide +kernel
      have hl : raw19423step3Labels = raw19423step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node854 node854Labels := by rfl

def raw19424 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, -1, 4]]
def raw19424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, -1, 4]]
def raw19424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![3, -3, 0], ![-3, -1, 4]]
def raw19424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19424step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![3, -3, 0], ![-3, -1, 4]]
def raw19424step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19424step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -3, 4], ![-3, 3, 0]]
def raw19424step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19424step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 3, -4], ![3, -3, 0]]
def raw19424step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19424 raw19424Labels = mixedMoment B node861 node861Labels := by
  calc
    mixedMoment B raw19424 raw19424Labels = mixedMoment B raw19424step0 raw19424step0Labels := by
      have hz : ∀ j, raw19424 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19424step0 = (fun i j => raw19424 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19424step0 raw19424; decide +kernel
      have hl : raw19424step0Labels = raw19424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19424 raw19424Labels permutation434 hz
    mixedMoment B raw19424step0 raw19424step0Labels = mixedMoment B raw19424step1 raw19424step1Labels := by
      have hz : ∀ j, raw19424step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19424step1 = (fun i j => raw19424step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19424step1 raw19424step0; decide +kernel
      have hl : raw19424step1Labels = raw19424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19424step0 raw19424step0Labels permutation80 hz
    mixedMoment B raw19424step1 raw19424step1Labels = mixedMoment B raw19424step2 raw19424step2Labels := by
      have hz : ∀ j, raw19424step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19424step2 = (fun i j => raw19424step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19424step2 raw19424step1; decide +kernel
      have hl : raw19424step2Labels = raw19424step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19424step1 raw19424step1Labels permutation14 hz
    mixedMoment B raw19424step2 raw19424step2Labels = mixedMoment B raw19424step3 raw19424step3Labels := by
      have ha : raw19424step3 = (fun i j => raw19424step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19424step3 raw19424step2; decide +kernel
      have hl : raw19424step3Labels = raw19424step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19424step2 raw19424step2Labels permutation3 permutation4
    mixedMoment B raw19424step3 raw19424step3Labels = mixedMoment B raw19424step4 raw19424step4Labels := by
      have ha : raw19424step4 = -raw19424step3 := by apply Matrix.ext; change ∀ i j, raw19424step4 i j = -(raw19424step3 i j); unfold raw19424step4 raw19424step3; decide +kernel
      have hl : raw19424step4Labels = raw19424step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node861 node861Labels := by rfl

def raw19425 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -2, 4]]
def raw19425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -2, 4]]
def raw19425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![-2, -2, 4]]
def raw19425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19425step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-2, -2, 4]]
def raw19425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19425step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-2, 2, 0], ![-2, -2, 4]]
def raw19425step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19425step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -2, 0], ![2, 2, -4]]
def raw19425step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19425 raw19425Labels = mixedMoment B node862 node862Labels := by
  calc
    mixedMoment B raw19425 raw19425Labels = mixedMoment B raw19425step0 raw19425step0Labels := by
      have hz : ∀ j, raw19425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19425step0 = (fun i j => raw19425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19425step0 raw19425; decide +kernel
      have hl : raw19425step0Labels = raw19425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19425 raw19425Labels permutation434 hz
    mixedMoment B raw19425step0 raw19425step0Labels = mixedMoment B raw19425step1 raw19425step1Labels := by
      have hz : ∀ j, raw19425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19425step1 = (fun i j => raw19425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19425step1 raw19425step0; decide +kernel
      have hl : raw19425step1Labels = raw19425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19425step0 raw19425step0Labels permutation80 hz
    mixedMoment B raw19425step1 raw19425step1Labels = mixedMoment B raw19425step2 raw19425step2Labels := by
      have hz : ∀ j, raw19425step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19425step2 = (fun i j => raw19425step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19425step2 raw19425step1; decide +kernel
      have hl : raw19425step2Labels = raw19425step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19425step1 raw19425step1Labels permutation14 hz
    mixedMoment B raw19425step2 raw19425step2Labels = mixedMoment B raw19425step3 raw19425step3Labels := by
      have ha : raw19425step3 = (fun i j => raw19425step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19425step3 raw19425step2; decide +kernel
      have hl : raw19425step3Labels = raw19425step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19425step2 raw19425step2Labels permutation2 permutation4
    mixedMoment B raw19425step3 raw19425step3Labels = mixedMoment B raw19425step4 raw19425step4Labels := by
      have ha : raw19425step4 = -raw19425step3 := by apply Matrix.ext; change ∀ i j, raw19425step4 i j = -(raw19425step3 i j); unfold raw19425step4 raw19425step3; decide +kernel
      have hl : raw19425step4Labels = raw19425step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node862 node862Labels := by rfl

def raw19426 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19426step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw19426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19426 raw19426Labels = mixedMoment B node1749 node1749Labels := by
  calc
    mixedMoment B raw19426 raw19426Labels = mixedMoment B raw19426step0 raw19426step0Labels := by
      have hz : ∀ j, raw19426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19426step0 = (fun i j => raw19426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19426step0 raw19426; decide +kernel
      have hl : raw19426step0Labels = raw19426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19426 raw19426Labels permutation434 hz
    mixedMoment B raw19426step0 raw19426step0Labels = mixedMoment B raw19426step1 raw19426step1Labels := by
      have hz : ∀ j, raw19426step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19426step1 = (fun i j => raw19426step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19426step1 raw19426step0; decide +kernel
      have hl : raw19426step1Labels = raw19426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19426step0 raw19426step0Labels permutation80 hz
    mixedMoment B raw19426step1 raw19426step1Labels = mixedMoment B raw19426step2 raw19426step2Labels := by
      have ha : raw19426step2 = (fun i j => raw19426step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19426step2 raw19426step1; decide +kernel
      have hl : raw19426step2Labels = raw19426step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19426step1 raw19426step1Labels permutation29 permutation2
    _ = mixedMoment B node1749 node1749Labels := by rfl

def raw19427 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19427step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19427step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw19427step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19427 raw19427Labels = mixedMoment B node1749 node1749Labels := by
  calc
    mixedMoment B raw19427 raw19427Labels = mixedMoment B raw19427step0 raw19427step0Labels := by
      have hz : ∀ j, raw19427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19427step0 = (fun i j => raw19427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19427step0 raw19427; decide +kernel
      have hl : raw19427step0Labels = raw19427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19427 raw19427Labels permutation434 hz
    mixedMoment B raw19427step0 raw19427step0Labels = mixedMoment B raw19427step1 raw19427step1Labels := by
      have hz : ∀ j, raw19427step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19427step1 = (fun i j => raw19427step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19427step1 raw19427step0; decide +kernel
      have hl : raw19427step1Labels = raw19427step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19427step0 raw19427step0Labels permutation56 hz
    mixedMoment B raw19427step1 raw19427step1Labels = mixedMoment B raw19427step2 raw19427step2Labels := by
      have ha : raw19427step2 = (fun i j => raw19427step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19427step2 raw19427step1; decide +kernel
      have hl : raw19427step2Labels = raw19427step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19427step1 raw19427step1Labels permutation29 permutation2
    _ = mixedMoment B node1749 node1749Labels := by rfl

def raw19428 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19428step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw19428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19428 raw19428Labels = mixedMoment B node1749 node1749Labels := by
  calc
    mixedMoment B raw19428 raw19428Labels = mixedMoment B raw19428step0 raw19428step0Labels := by
      have hz : ∀ j, raw19428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19428step0 = (fun i j => raw19428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19428step0 raw19428; decide +kernel
      have hl : raw19428step0Labels = raw19428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19428 raw19428Labels permutation346 hz
    mixedMoment B raw19428step0 raw19428step0Labels = mixedMoment B raw19428step1 raw19428step1Labels := by
      have hz : ∀ j, raw19428step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19428step1 = (fun i j => raw19428step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19428step1 raw19428step0; decide +kernel
      have hl : raw19428step1Labels = raw19428step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19428step0 raw19428step0Labels permutation56 hz
    mixedMoment B raw19428step1 raw19428step1Labels = mixedMoment B raw19428step2 raw19428step2Labels := by
      have ha : raw19428step2 = (fun i j => raw19428step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19428step2 raw19428step1; decide +kernel
      have hl : raw19428step2Labels = raw19428step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19428step1 raw19428step1Labels permutation29 permutation2
    _ = mixedMoment B node1749 node1749Labels := by rfl

def raw19429 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19429step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19429step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19429step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19429step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19429step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19429 raw19429Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19429 raw19429Labels = mixedMoment B raw19429step0 raw19429step0Labels := by
      have hz : ∀ j, raw19429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19429step0 = (fun i j => raw19429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19429step0 raw19429; decide +kernel
      have hl : raw19429step0Labels = raw19429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19429 raw19429Labels permutation434 hz
    mixedMoment B raw19429step0 raw19429step0Labels = mixedMoment B raw19429step1 raw19429step1Labels := by
      have hz : ∀ j, raw19429step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19429step1 = (fun i j => raw19429step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19429step1 raw19429step0; decide +kernel
      have hl : raw19429step1Labels = raw19429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19429step0 raw19429step0Labels permutation80 hz
    mixedMoment B raw19429step1 raw19429step1Labels = mixedMoment B raw19429step2 raw19429step2Labels := by
      have hz : ∀ j, raw19429step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19429step2 = (fun i j => raw19429step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19429step2 raw19429step1; decide +kernel
      have hl : raw19429step2Labels = raw19429step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19429step1 raw19429step1Labels permutation14 hz
    mixedMoment B raw19429step2 raw19429step2Labels = mixedMoment B raw19429step3 raw19429step3Labels := by
      have ha : raw19429step3 = (fun i j => raw19429step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19429step3 raw19429step2; decide +kernel
      have hl : raw19429step3Labels = raw19429step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19429step2 raw19429step2Labels permutation2 permutation4
    mixedMoment B raw19429step3 raw19429step3Labels = mixedMoment B raw19429step4 raw19429step4Labels := by
      have ha : raw19429step4 = -raw19429step3 := by apply Matrix.ext; change ∀ i j, raw19429step4 i j = -(raw19429step3 i j); unfold raw19429step4 raw19429step3; decide +kernel
      have hl : raw19429step4Labels = raw19429step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw19430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![4, 0, -4]]
def raw19430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![4, 0, -4]]
def raw19430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -3, 3], ![4, 0, -4]]
def raw19430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19430step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![4, 0, -4]]
def raw19430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19430step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-4, 3, 1]]
def raw19430step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19430step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![4, -3, -1]]
def raw19430step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19430 raw19430Labels = mixedMoment B node839 node839Labels := by
  calc
    mixedMoment B raw19430 raw19430Labels = mixedMoment B raw19430step0 raw19430step0Labels := by
      have hz : ∀ j, raw19430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19430step0 = (fun i j => raw19430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19430step0 raw19430; decide +kernel
      have hl : raw19430step0Labels = raw19430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19430 raw19430Labels permutation434 hz
    mixedMoment B raw19430step0 raw19430step0Labels = mixedMoment B raw19430step1 raw19430step1Labels := by
      have hz : ∀ j, raw19430step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19430step1 = (fun i j => raw19430step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19430step1 raw19430step0; decide +kernel
      have hl : raw19430step1Labels = raw19430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19430step0 raw19430step0Labels permutation80 hz
    mixedMoment B raw19430step1 raw19430step1Labels = mixedMoment B raw19430step2 raw19430step2Labels := by
      have hz : ∀ j, raw19430step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19430step2 = (fun i j => raw19430step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19430step2 raw19430step1; decide +kernel
      have hl : raw19430step2Labels = raw19430step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19430step1 raw19430step1Labels permutation14 hz
    mixedMoment B raw19430step2 raw19430step2Labels = mixedMoment B raw19430step3 raw19430step3Labels := by
      have ha : raw19430step3 = (fun i j => raw19430step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19430step3 raw19430step2; decide +kernel
      have hl : raw19430step3Labels = raw19430step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19430step2 raw19430step2Labels permutation7 permutation2
    mixedMoment B raw19430step3 raw19430step3Labels = mixedMoment B raw19430step4 raw19430step4Labels := by
      have ha : raw19430step4 = -raw19430step3 := by apply Matrix.ext; change ∀ i j, raw19430step4 i j = -(raw19430step3 i j); unfold raw19430step4 raw19430step3; decide +kernel
      have hl : raw19430step4Labels = raw19430step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node839 node839Labels := by rfl

def raw19431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![4, 0, -4]]
def raw19431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3], ![4, 0, -4]]
def raw19431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19431step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -3, 3], ![4, 0, -4]]
def raw19431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19431step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 1, 0], ![-3, 2, 1]]
def raw19431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19431step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw19431step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19431 raw19431Labels = mixedMoment B node836 node836Labels := by
  calc
    mixedMoment B raw19431 raw19431Labels = mixedMoment B raw19431step0 raw19431step0Labels := by
      have hz : ∀ j, raw19431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19431step0 = (fun i j => raw19431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19431step0 raw19431; decide +kernel
      have hl : raw19431step0Labels = raw19431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19431 raw19431Labels permutation434 hz
    mixedMoment B raw19431step0 raw19431step0Labels = mixedMoment B raw19431step1 raw19431step1Labels := by
      have hz : ∀ j, raw19431step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19431step1 = (fun i j => raw19431step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19431step1 raw19431step0; decide +kernel
      have hl : raw19431step1Labels = raw19431step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19431step0 raw19431step0Labels permutation80 hz
    mixedMoment B raw19431step1 raw19431step1Labels = mixedMoment B raw19431step2 raw19431step2Labels := by
      have ha : raw19431step2 = (fun i j => raw19431step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19431step2 raw19431step1; decide +kernel
      have hl : raw19431step2Labels = raw19431step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19431step1 raw19431step1Labels permutation31 permutation2
    mixedMoment B raw19431step2 raw19431step2Labels = mixedMoment B raw19431step3 raw19431step3Labels := by
      have ha : raw19431step3 = -raw19431step2 := by apply Matrix.ext; change ∀ i j, raw19431step3 i j = -(raw19431step2 i j); unfold raw19431step3 raw19431step2; decide +kernel
      have hl : raw19431step3Labels = raw19431step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node836 node836Labels := by rfl

def raw19432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3], ![4, 0, -4]]
def raw19432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3], ![4, 0, -4]]
def raw19432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -3, 3], ![4, 0, -4]]
def raw19432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19432step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 1, 0], ![-3, 2, 1]]
def raw19432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19432step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw19432step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19432 raw19432Labels = mixedMoment B node836 node836Labels := by
  calc
    mixedMoment B raw19432 raw19432Labels = mixedMoment B raw19432step0 raw19432step0Labels := by
      have hz : ∀ j, raw19432 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19432step0 = (fun i j => raw19432 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19432step0 raw19432; decide +kernel
      have hl : raw19432step0Labels = raw19432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19432 raw19432Labels permutation434 hz
    mixedMoment B raw19432step0 raw19432step0Labels = mixedMoment B raw19432step1 raw19432step1Labels := by
      have hz : ∀ j, raw19432step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19432step1 = (fun i j => raw19432step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19432step1 raw19432step0; decide +kernel
      have hl : raw19432step1Labels = raw19432step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19432step0 raw19432step0Labels permutation56 hz
    mixedMoment B raw19432step1 raw19432step1Labels = mixedMoment B raw19432step2 raw19432step2Labels := by
      have ha : raw19432step2 = (fun i j => raw19432step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19432step2 raw19432step1; decide +kernel
      have hl : raw19432step2Labels = raw19432step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19432step1 raw19432step1Labels permutation31 permutation2
    mixedMoment B raw19432step2 raw19432step2Labels = mixedMoment B raw19432step3 raw19432step3Labels := by
      have ha : raw19432step3 = -raw19432step2 := by apply Matrix.ext; change ∀ i j, raw19432step3 i j = -(raw19432step2 i j); unfold raw19432step3 raw19432step2; decide +kernel
      have hl : raw19432step3Labels = raw19432step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node836 node836Labels := by rfl

def raw19433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3], ![4, 0, -4]]
def raw19433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3], ![4, 0, -4]]
def raw19433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -3, 3], ![4, 0, -4]]
def raw19433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19433step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 1, 0], ![-3, 2, 1]]
def raw19433step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19433step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw19433step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19433 raw19433Labels = mixedMoment B node836 node836Labels := by
  calc
    mixedMoment B raw19433 raw19433Labels = mixedMoment B raw19433step0 raw19433step0Labels := by
      have hz : ∀ j, raw19433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19433step0 = (fun i j => raw19433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19433step0 raw19433; decide +kernel
      have hl : raw19433step0Labels = raw19433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19433 raw19433Labels permutation346 hz
    mixedMoment B raw19433step0 raw19433step0Labels = mixedMoment B raw19433step1 raw19433step1Labels := by
      have hz : ∀ j, raw19433step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19433step1 = (fun i j => raw19433step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19433step1 raw19433step0; decide +kernel
      have hl : raw19433step1Labels = raw19433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19433step0 raw19433step0Labels permutation56 hz
    mixedMoment B raw19433step1 raw19433step1Labels = mixedMoment B raw19433step2 raw19433step2Labels := by
      have ha : raw19433step2 = (fun i j => raw19433step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19433step2 raw19433step1; decide +kernel
      have hl : raw19433step2Labels = raw19433step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19433step1 raw19433step1Labels permutation31 permutation2
    mixedMoment B raw19433step2 raw19433step2Labels = mixedMoment B raw19433step3 raw19433step3Labels := by
      have ha : raw19433step3 = -raw19433step2 := by apply Matrix.ext; change ∀ i j, raw19433step3 i j = -(raw19433step2 i j); unfold raw19433step3 raw19433step2; decide +kernel
      have hl : raw19433step3Labels = raw19433step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node836 node836Labels := by rfl

def raw19434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3], ![4, 0, -4]]
def raw19434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3], ![4, 0, -4]]
def raw19434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -2, 3], ![4, 0, -4]]
def raw19434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19434step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![4, 0, -4]]
def raw19434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19434step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -2, 3], ![-3, 2, 1]]
def raw19434step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19434step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw19434step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19434 raw19434Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw19434 raw19434Labels = mixedMoment B raw19434step0 raw19434step0Labels := by
      have hz : ∀ j, raw19434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19434step0 = (fun i j => raw19434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19434step0 raw19434; decide +kernel
      have hl : raw19434step0Labels = raw19434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19434 raw19434Labels permutation434 hz
    mixedMoment B raw19434step0 raw19434step0Labels = mixedMoment B raw19434step1 raw19434step1Labels := by
      have hz : ∀ j, raw19434step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19434step1 = (fun i j => raw19434step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19434step1 raw19434step0; decide +kernel
      have hl : raw19434step1Labels = raw19434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19434step0 raw19434step0Labels permutation80 hz
    mixedMoment B raw19434step1 raw19434step1Labels = mixedMoment B raw19434step2 raw19434step2Labels := by
      have hz : ∀ j, raw19434step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19434step2 = (fun i j => raw19434step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19434step2 raw19434step1; decide +kernel
      have hl : raw19434step2Labels = raw19434step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19434step1 raw19434step1Labels permutation14 hz
    mixedMoment B raw19434step2 raw19434step2Labels = mixedMoment B raw19434step3 raw19434step3Labels := by
      have ha : raw19434step3 = (fun i j => raw19434step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19434step3 raw19434step2; decide +kernel
      have hl : raw19434step3Labels = raw19434step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19434step2 raw19434step2Labels permutation7 permutation2
    mixedMoment B raw19434step3 raw19434step3Labels = mixedMoment B raw19434step4 raw19434step4Labels := by
      have ha : raw19434step4 = -raw19434step3 := by apply Matrix.ext; change ∀ i j, raw19434step4 i j = -(raw19434step3 i j); unfold raw19434step4 raw19434step3; decide +kernel
      have hl : raw19434step4Labels = raw19434step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node860 node860Labels := by rfl

def raw19435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![3, 1, -4]]
def raw19435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![3, 1, -4]]
def raw19435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -3, 3], ![3, 1, -4]]
def raw19435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19435step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![3, 1, -4]]
def raw19435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19435step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-3, 2, 1]]
def raw19435step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19435step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw19435step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19435 raw19435Labels = mixedMoment B node1747 node1747Labels := by
  calc
    mixedMoment B raw19435 raw19435Labels = mixedMoment B raw19435step0 raw19435step0Labels := by
      have hz : ∀ j, raw19435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19435step0 = (fun i j => raw19435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19435step0 raw19435; decide +kernel
      have hl : raw19435step0Labels = raw19435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19435 raw19435Labels permutation434 hz
    mixedMoment B raw19435step0 raw19435step0Labels = mixedMoment B raw19435step1 raw19435step1Labels := by
      have hz : ∀ j, raw19435step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19435step1 = (fun i j => raw19435step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19435step1 raw19435step0; decide +kernel
      have hl : raw19435step1Labels = raw19435step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19435step0 raw19435step0Labels permutation80 hz
    mixedMoment B raw19435step1 raw19435step1Labels = mixedMoment B raw19435step2 raw19435step2Labels := by
      have hz : ∀ j, raw19435step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19435step2 = (fun i j => raw19435step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19435step2 raw19435step1; decide +kernel
      have hl : raw19435step2Labels = raw19435step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19435step1 raw19435step1Labels permutation14 hz
    mixedMoment B raw19435step2 raw19435step2Labels = mixedMoment B raw19435step3 raw19435step3Labels := by
      have ha : raw19435step3 = (fun i j => raw19435step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19435step3 raw19435step2; decide +kernel
      have hl : raw19435step3Labels = raw19435step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19435step2 raw19435step2Labels permutation7 permutation2
    mixedMoment B raw19435step3 raw19435step3Labels = mixedMoment B raw19435step4 raw19435step4Labels := by
      have ha : raw19435step4 = -raw19435step3 := by apply Matrix.ext; change ∀ i j, raw19435step4 i j = -(raw19435step3 i j); unfold raw19435step4 raw19435step3; decide +kernel
      have hl : raw19435step4Labels = raw19435step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1747 node1747Labels := by rfl

def raw19436 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![0, 0], ![-3, 3], ![4, -4]]
def raw19436Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19436step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-3, 3], ![4, -4]]
def raw19436step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19436step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-3, 3], ![4, -4]]
def raw19436step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19436step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![4, -4]]
def raw19436step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19436step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw19436step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19436step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw19436step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19436 raw19436Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw19436 raw19436Labels = mixedMoment B raw19436step0 raw19436step0Labels := by
      have hz : ∀ j, raw19436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19436step0 = (fun i j => raw19436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19436step0 raw19436; decide +kernel
      have hl : raw19436step0Labels = raw19436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19436 raw19436Labels permutation434 hz
    mixedMoment B raw19436step0 raw19436step0Labels = mixedMoment B raw19436step1 raw19436step1Labels := by
      have hz : ∀ j, raw19436step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19436step1 = (fun i j => raw19436step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19436step1 raw19436step0; decide +kernel
      have hl : raw19436step1Labels = raw19436step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19436step0 raw19436step0Labels permutation80 hz
    mixedMoment B raw19436step1 raw19436step1Labels = mixedMoment B raw19436step2 raw19436step2Labels := by
      have hz : ∀ j, raw19436step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19436step2 = (fun i j => raw19436step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19436step2 raw19436step1; decide +kernel
      have hl : raw19436step2Labels = raw19436step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19436step1 raw19436step1Labels permutation14 hz
    mixedMoment B raw19436step2 raw19436step2Labels = mixedMoment B raw19436step3 raw19436step3Labels := by
      have ha : raw19436step3 = (fun i j => raw19436step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19436step3 raw19436step2; decide +kernel
      have hl : raw19436step3Labels = raw19436step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19436step2 raw19436step2Labels permutation6 permutation0
    mixedMoment B raw19436step3 raw19436step3Labels = mixedMoment B raw19436step4 raw19436step4Labels := by
      have ha : raw19436step4 = -raw19436step3 := by apply Matrix.ext; change ∀ i j, raw19436step4 i j = -(raw19436step3 i j); unfold raw19436step4 raw19436step3; decide +kernel
      have hl : raw19436step4Labels = raw19436step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw19437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19437step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19437 raw19437Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw19437 raw19437Labels = mixedMoment B raw19437step0 raw19437step0Labels := by
      have hz : ∀ j, raw19437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19437step0 = (fun i j => raw19437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19437step0 raw19437; decide +kernel
      have hl : raw19437step0Labels = raw19437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19437 raw19437Labels permutation346 hz
    mixedMoment B raw19437step0 raw19437step0Labels = mixedMoment B raw19437step1 raw19437step1Labels := by
      have hz : ∀ j, raw19437step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19437step1 = (fun i j => raw19437step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19437step1 raw19437step0; decide +kernel
      have hl : raw19437step1Labels = raw19437step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19437step0 raw19437step0Labels permutation56 hz
    mixedMoment B raw19437step1 raw19437step1Labels = mixedMoment B raw19437step2 raw19437step2Labels := by
      have ha : raw19437step2 = (fun i j => raw19437step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19437step2 raw19437step1; decide +kernel
      have hl : raw19437step2Labels = raw19437step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19437step1 raw19437step1Labels permutation10 permutation2
    _ = mixedMoment B node587 node587Labels := by rfl

def raw19438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19438 raw19438Labels = mixedMoment B node911 node911Labels := by
  calc
    mixedMoment B raw19438 raw19438Labels = mixedMoment B raw19438step0 raw19438step0Labels := by
      have hz : ∀ j, raw19438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19438step0 = (fun i j => raw19438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19438step0 raw19438; decide +kernel
      have hl : raw19438step0Labels = raw19438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19438 raw19438Labels permutation346 hz
    mixedMoment B raw19438step0 raw19438step0Labels = mixedMoment B raw19438step1 raw19438step1Labels := by
      have ha : raw19438step1 = (fun i j => raw19438step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19438step1 raw19438step0; decide +kernel
      have hl : raw19438step1Labels = raw19438step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19438step0 raw19438step0Labels permutation34 permutation2
    _ = mixedMoment B node911 node911Labels := by rfl

def raw19439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19439 raw19439Labels = mixedMoment B node911 node911Labels := by
  calc
    mixedMoment B raw19439 raw19439Labels = mixedMoment B raw19439step0 raw19439step0Labels := by
      have hz : ∀ j, raw19439 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19439step0 = (fun i j => raw19439 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19439step0 raw19439; decide +kernel
      have hl : raw19439step0Labels = raw19439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19439 raw19439Labels permutation265 hz
    mixedMoment B raw19439step0 raw19439step0Labels = mixedMoment B raw19439step1 raw19439step1Labels := by
      have ha : raw19439step1 = (fun i j => raw19439step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19439step1 raw19439step0; decide +kernel
      have hl : raw19439step1Labels = raw19439step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19439step0 raw19439step0Labels permutation34 permutation2
    _ = mixedMoment B node911 node911Labels := by rfl

def raw19440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19440step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19440 raw19440Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw19440 raw19440Labels = mixedMoment B raw19440step0 raw19440step0Labels := by
      have hz : ∀ j, raw19440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19440step0 = (fun i j => raw19440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19440step0 raw19440; decide +kernel
      have hl : raw19440step0Labels = raw19440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19440 raw19440Labels permutation346 hz
    mixedMoment B raw19440step0 raw19440step0Labels = mixedMoment B raw19440step1 raw19440step1Labels := by
      have hz : ∀ j, raw19440step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19440step1 = (fun i j => raw19440step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19440step1 raw19440step0; decide +kernel
      have hl : raw19440step1Labels = raw19440step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19440step0 raw19440step0Labels permutation56 hz
    _ = mixedMoment B node1027 node1027Labels := by rfl

def raw19441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw19441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw19441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19441step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw19441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19441step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw19441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19441 raw19441Labels = mixedMoment B node951 node951Labels := by
  calc
    mixedMoment B raw19441 raw19441Labels = mixedMoment B raw19441step0 raw19441step0Labels := by
      have hz : ∀ j, raw19441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19441step0 = (fun i j => raw19441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19441step0 raw19441; decide +kernel
      have hl : raw19441step0Labels = raw19441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19441 raw19441Labels permutation346 hz
    mixedMoment B raw19441step0 raw19441step0Labels = mixedMoment B raw19441step1 raw19441step1Labels := by
      have hz : ∀ j, raw19441step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19441step1 = (fun i j => raw19441step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19441step1 raw19441step0; decide +kernel
      have hl : raw19441step1Labels = raw19441step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19441step0 raw19441step0Labels permutation56 hz
    mixedMoment B raw19441step1 raw19441step1Labels = mixedMoment B raw19441step2 raw19441step2Labels := by
      have ha : raw19441step2 = (fun i j => raw19441step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19441step2 raw19441step1; decide +kernel
      have hl : raw19441step2Labels = raw19441step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19441step1 raw19441step1Labels permutation10 permutation2
    _ = mixedMoment B node951 node951Labels := by rfl

def raw19442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw19442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw19442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19442step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw19442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19442step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw19442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19442 raw19442Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw19442 raw19442Labels = mixedMoment B raw19442step0 raw19442step0Labels := by
      have hz : ∀ j, raw19442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19442step0 = (fun i j => raw19442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19442step0 raw19442; decide +kernel
      have hl : raw19442step0Labels = raw19442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19442 raw19442Labels permutation346 hz
    mixedMoment B raw19442step0 raw19442step0Labels = mixedMoment B raw19442step1 raw19442step1Labels := by
      have hz : ∀ j, raw19442step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19442step1 = (fun i j => raw19442step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19442step1 raw19442step0; decide +kernel
      have hl : raw19442step1Labels = raw19442step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19442step0 raw19442step0Labels permutation56 hz
    mixedMoment B raw19442step1 raw19442step1Labels = mixedMoment B raw19442step2 raw19442step2Labels := by
      have ha : raw19442step2 = (fun i j => raw19442step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19442step2 raw19442step1; decide +kernel
      have hl : raw19442step2Labels = raw19442step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19442step1 raw19442step1Labels permutation10 permutation2
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw19443 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw19443Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19443step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw19443step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19443step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw19443step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19443 raw19443Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw19443 raw19443Labels = mixedMoment B raw19443step0 raw19443step0Labels := by
      have hz : ∀ j, raw19443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19443step0 = (fun i j => raw19443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19443step0 raw19443; decide +kernel
      have hl : raw19443step0Labels = raw19443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19443 raw19443Labels permutation346 hz
    mixedMoment B raw19443step0 raw19443step0Labels = mixedMoment B raw19443step1 raw19443step1Labels := by
      have hz : ∀ j, raw19443step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19443step1 = (fun i j => raw19443step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19443step1 raw19443step0; decide +kernel
      have hl : raw19443step1Labels = raw19443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19443step0 raw19443step0Labels permutation56 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw19444 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19444 raw19444Labels = mixedMoment B node1615 node1615Labels := by
  calc
    mixedMoment B raw19444 raw19444Labels = mixedMoment B raw19444step0 raw19444step0Labels := by
      have hz : ∀ j, raw19444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19444step0 = (fun i j => raw19444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19444step0 raw19444; decide +kernel
      have hl : raw19444step0Labels = raw19444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19444 raw19444Labels permutation346 hz
    mixedMoment B raw19444step0 raw19444step0Labels = mixedMoment B raw19444step1 raw19444step1Labels := by
      have ha : raw19444step1 = (fun i j => raw19444step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19444step1 raw19444step0; decide +kernel
      have hl : raw19444step1Labels = raw19444step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19444step0 raw19444step0Labels permutation137 permutation2
    _ = mixedMoment B node1615 node1615Labels := by rfl

def raw19445 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19445 raw19445Labels = mixedMoment B node1615 node1615Labels := by
  calc
    mixedMoment B raw19445 raw19445Labels = mixedMoment B raw19445step0 raw19445step0Labels := by
      have hz : ∀ j, raw19445 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19445step0 = (fun i j => raw19445 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19445step0 raw19445; decide +kernel
      have hl : raw19445step0Labels = raw19445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19445 raw19445Labels permutation265 hz
    mixedMoment B raw19445step0 raw19445step0Labels = mixedMoment B raw19445step1 raw19445step1Labels := by
      have ha : raw19445step1 = (fun i j => raw19445step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19445step1 raw19445step0; decide +kernel
      have hl : raw19445step1Labels = raw19445step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19445step0 raw19445step0Labels permutation137 permutation2
    _ = mixedMoment B node1615 node1615Labels := by rfl

def raw19446 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19446step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19446step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19446 raw19446Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19446 raw19446Labels = mixedMoment B raw19446step0 raw19446step0Labels := by
      have hz : ∀ j, raw19446 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19446step0 = (fun i j => raw19446 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19446step0 raw19446; decide +kernel
      have hl : raw19446step0Labels = raw19446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19446 raw19446Labels permutation520 hz
    mixedMoment B raw19446step0 raw19446step0Labels = mixedMoment B raw19446step1 raw19446step1Labels := by
      have hz : ∀ j, raw19446step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19446step1 = (fun i j => raw19446step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19446step1 raw19446step0; decide +kernel
      have hl : raw19446step1Labels = raw19446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19446step0 raw19446step0Labels permutation80 hz
    mixedMoment B raw19446step1 raw19446step1Labels = mixedMoment B raw19446step2 raw19446step2Labels := by
      have hz : ∀ j, raw19446step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19446step2 = (fun i j => raw19446step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19446step2 raw19446step1; decide +kernel
      have hl : raw19446step2Labels = raw19446step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19446step1 raw19446step1Labels permutation14 hz
    mixedMoment B raw19446step2 raw19446step2Labels = mixedMoment B raw19446step3 raw19446step3Labels := by
      have ha : raw19446step3 = (fun i j => raw19446step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19446step3 raw19446step2; decide +kernel
      have hl : raw19446step3Labels = raw19446step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19446step2 raw19446step2Labels permutation7 permutation2
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw19447 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 0, 4]]
def raw19447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-4, 0, 4]]
def raw19447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-4, 0, 4]]
def raw19447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19447step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19447 raw19447Labels = mixedMoment B node849 node849Labels := by
  calc
    mixedMoment B raw19447 raw19447Labels = mixedMoment B raw19447step0 raw19447step0Labels := by
      have hz : ∀ j, raw19447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19447step0 = (fun i j => raw19447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19447step0 raw19447; decide +kernel
      have hl : raw19447step0Labels = raw19447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19447 raw19447Labels permutation346 hz
    mixedMoment B raw19447step0 raw19447step0Labels = mixedMoment B raw19447step1 raw19447step1Labels := by
      have hz : ∀ j, raw19447step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19447step1 = (fun i j => raw19447step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19447step1 raw19447step0; decide +kernel
      have hl : raw19447step1Labels = raw19447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19447step0 raw19447step0Labels permutation56 hz
    mixedMoment B raw19447step1 raw19447step1Labels = mixedMoment B raw19447step2 raw19447step2Labels := by
      have ha : raw19447step2 = (fun i j => raw19447step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19447step2 raw19447step1; decide +kernel
      have hl : raw19447step2Labels = raw19447step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19447step1 raw19447step1Labels permutation29 permutation2
    _ = mixedMoment B node849 node849Labels := by rfl

def raw19448 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw19448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19448 raw19448Labels = mixedMoment B node846 node846Labels := by
  calc
    mixedMoment B raw19448 raw19448Labels = mixedMoment B raw19448step0 raw19448step0Labels := by
      have hz : ∀ j, raw19448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19448step0 = (fun i j => raw19448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19448step0 raw19448; decide +kernel
      have hl : raw19448step0Labels = raw19448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19448 raw19448Labels permutation346 hz
    mixedMoment B raw19448step0 raw19448step0Labels = mixedMoment B raw19448step1 raw19448step1Labels := by
      have ha : raw19448step1 = (fun i j => raw19448step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19448step1 raw19448step0; decide +kernel
      have hl : raw19448step1Labels = raw19448step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19448step0 raw19448step0Labels permutation32 permutation4
    mixedMoment B raw19448step1 raw19448step1Labels = mixedMoment B raw19448step2 raw19448step2Labels := by
      have ha : raw19448step2 = -raw19448step1 := by apply Matrix.ext; change ∀ i j, raw19448step2 i j = -(raw19448step1 i j); unfold raw19448step2 raw19448step1; decide +kernel
      have hl : raw19448step2Labels = raw19448step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node846 node846Labels := by rfl

def raw19449 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw19449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19449 raw19449Labels = mixedMoment B node846 node846Labels := by
  calc
    mixedMoment B raw19449 raw19449Labels = mixedMoment B raw19449step0 raw19449step0Labels := by
      have hz : ∀ j, raw19449 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19449step0 = (fun i j => raw19449 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19449step0 raw19449; decide +kernel
      have hl : raw19449step0Labels = raw19449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19449 raw19449Labels permutation265 hz
    mixedMoment B raw19449step0 raw19449step0Labels = mixedMoment B raw19449step1 raw19449step1Labels := by
      have ha : raw19449step1 = (fun i j => raw19449step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19449step1 raw19449step0; decide +kernel
      have hl : raw19449step1Labels = raw19449step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19449step0 raw19449step0Labels permutation32 permutation4
    mixedMoment B raw19449step1 raw19449step1Labels = mixedMoment B raw19449step2 raw19449step2Labels := by
      have ha : raw19449step2 = -raw19449step1 := by apply Matrix.ext; change ∀ i j, raw19449step2 i j = -(raw19449step1 i j); unfold raw19449step2 raw19449step1; decide +kernel
      have hl : raw19449step2Labels = raw19449step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node846 node846Labels := by rfl

def raw19450 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19450step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -3, 4], ![-2, 2, 0]]
def raw19450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19450step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 3, -4], ![2, -2, 0]]
def raw19450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19450 raw19450Labels = mixedMoment B node854 node854Labels := by
  calc
    mixedMoment B raw19450 raw19450Labels = mixedMoment B raw19450step0 raw19450step0Labels := by
      have hz : ∀ j, raw19450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19450step0 = (fun i j => raw19450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19450step0 raw19450; decide +kernel
      have hl : raw19450step0Labels = raw19450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19450 raw19450Labels permutation346 hz
    mixedMoment B raw19450step0 raw19450step0Labels = mixedMoment B raw19450step1 raw19450step1Labels := by
      have hz : ∀ j, raw19450step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19450step1 = (fun i j => raw19450step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19450step1 raw19450step0; decide +kernel
      have hl : raw19450step1Labels = raw19450step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19450step0 raw19450step0Labels permutation56 hz
    mixedMoment B raw19450step1 raw19450step1Labels = mixedMoment B raw19450step2 raw19450step2Labels := by
      have ha : raw19450step2 = (fun i j => raw19450step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19450step2 raw19450step1; decide +kernel
      have hl : raw19450step2Labels = raw19450step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19450step1 raw19450step1Labels permutation11 permutation4
    mixedMoment B raw19450step2 raw19450step2Labels = mixedMoment B raw19450step3 raw19450step3Labels := by
      have ha : raw19450step3 = -raw19450step2 := by apply Matrix.ext; change ∀ i j, raw19450step3 i j = -(raw19450step2 i j); unfold raw19450step3 raw19450step2; decide +kernel
      have hl : raw19450step3Labels = raw19450step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node854 node854Labels := by rfl

def raw19451 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19451step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19451step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19451step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19451 raw19451Labels = mixedMoment B node849 node849Labels := by
  calc
    mixedMoment B raw19451 raw19451Labels = mixedMoment B raw19451step0 raw19451step0Labels := by
      have hz : ∀ j, raw19451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19451step0 = (fun i j => raw19451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19451step0 raw19451; decide +kernel
      have hl : raw19451step0Labels = raw19451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19451 raw19451Labels permutation346 hz
    mixedMoment B raw19451step0 raw19451step0Labels = mixedMoment B raw19451step1 raw19451step1Labels := by
      have hz : ∀ j, raw19451step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19451step1 = (fun i j => raw19451step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19451step1 raw19451step0; decide +kernel
      have hl : raw19451step1Labels = raw19451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19451step0 raw19451step0Labels permutation56 hz
    mixedMoment B raw19451step1 raw19451step1Labels = mixedMoment B raw19451step2 raw19451step2Labels := by
      have ha : raw19451step2 = (fun i j => raw19451step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19451step2 raw19451step1; decide +kernel
      have hl : raw19451step2Labels = raw19451step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19451step1 raw19451step1Labels permutation8 permutation4
    mixedMoment B raw19451step2 raw19451step2Labels = mixedMoment B raw19451step3 raw19451step3Labels := by
      have ha : raw19451step3 = -raw19451step2 := by apply Matrix.ext; change ∀ i j, raw19451step3 i j = -(raw19451step2 i j); unfold raw19451step3 raw19451step2; decide +kernel
      have hl : raw19451step3Labels = raw19451step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node849 node849Labels := by rfl

def raw19452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-4, 3, 1]]
def raw19452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![4, -3, -1]]
def raw19452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19452 raw19452Labels = mixedMoment B node797 node797Labels := by
  calc
    mixedMoment B raw19452 raw19452Labels = mixedMoment B raw19452step0 raw19452step0Labels := by
      have hz : ∀ j, raw19452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19452step0 = (fun i j => raw19452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19452step0 raw19452; decide +kernel
      have hl : raw19452step0Labels = raw19452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19452 raw19452Labels permutation346 hz
    mixedMoment B raw19452step0 raw19452step0Labels = mixedMoment B raw19452step1 raw19452step1Labels := by
      have hz : ∀ j, raw19452step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19452step1 = (fun i j => raw19452step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19452step1 raw19452step0; decide +kernel
      have hl : raw19452step1Labels = raw19452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19452step0 raw19452step0Labels permutation56 hz
    mixedMoment B raw19452step1 raw19452step1Labels = mixedMoment B raw19452step2 raw19452step2Labels := by
      have ha : raw19452step2 = (fun i j => raw19452step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19452step2 raw19452step1; decide +kernel
      have hl : raw19452step2Labels = raw19452step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19452step1 raw19452step1Labels permutation29 permutation2
    mixedMoment B raw19452step2 raw19452step2Labels = mixedMoment B raw19452step3 raw19452step3Labels := by
      have ha : raw19452step3 = -raw19452step2 := by apply Matrix.ext; change ∀ i j, raw19452step3 i j = -(raw19452step2 i j); unfold raw19452step3 raw19452step2; decide +kernel
      have hl : raw19452step3Labels = raw19452step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node797 node797Labels := by rfl

def raw19453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw19453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw19453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19453 raw19453Labels = mixedMoment B node794 node794Labels := by
  calc
    mixedMoment B raw19453 raw19453Labels = mixedMoment B raw19453step0 raw19453step0Labels := by
      have hz : ∀ j, raw19453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19453step0 = (fun i j => raw19453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19453step0 raw19453; decide +kernel
      have hl : raw19453step0Labels = raw19453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19453 raw19453Labels permutation346 hz
    mixedMoment B raw19453step0 raw19453step0Labels = mixedMoment B raw19453step1 raw19453step1Labels := by
      have ha : raw19453step1 = (fun i j => raw19453step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19453step1 raw19453step0; decide +kernel
      have hl : raw19453step1Labels = raw19453step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19453step0 raw19453step0Labels permutation145 permutation2
    mixedMoment B raw19453step1 raw19453step1Labels = mixedMoment B raw19453step2 raw19453step2Labels := by
      have ha : raw19453step2 = -raw19453step1 := by apply Matrix.ext; change ∀ i j, raw19453step2 i j = -(raw19453step1 i j); unfold raw19453step2 raw19453step1; decide +kernel
      have hl : raw19453step2Labels = raw19453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node794 node794Labels := by rfl

def raw19454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw19454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw19454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19454 raw19454Labels = mixedMoment B node794 node794Labels := by
  calc
    mixedMoment B raw19454 raw19454Labels = mixedMoment B raw19454step0 raw19454step0Labels := by
      have hz : ∀ j, raw19454 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19454step0 = (fun i j => raw19454 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19454step0 raw19454; decide +kernel
      have hl : raw19454step0Labels = raw19454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19454 raw19454Labels permutation265 hz
    mixedMoment B raw19454step0 raw19454step0Labels = mixedMoment B raw19454step1 raw19454step1Labels := by
      have ha : raw19454step1 = (fun i j => raw19454step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19454step1 raw19454step0; decide +kernel
      have hl : raw19454step1Labels = raw19454step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19454step0 raw19454step0Labels permutation145 permutation2
    mixedMoment B raw19454step1 raw19454step1Labels = mixedMoment B raw19454step2 raw19454step2Labels := by
      have ha : raw19454step2 = -raw19454step1 := by apply Matrix.ext; change ∀ i j, raw19454step2 i j = -(raw19454step1 i j); unfold raw19454step2 raw19454step1; decide +kernel
      have hl : raw19454step2Labels = raw19454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node794 node794Labels := by rfl

def raw19455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![4, 0, -4]]
def raw19455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw19455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19455step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw19455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19455 raw19455Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw19455 raw19455Labels = mixedMoment B raw19455step0 raw19455step0Labels := by
      have hz : ∀ j, raw19455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19455step0 = (fun i j => raw19455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19455step0 raw19455; decide +kernel
      have hl : raw19455step0Labels = raw19455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19455 raw19455Labels permutation346 hz
    mixedMoment B raw19455step0 raw19455step0Labels = mixedMoment B raw19455step1 raw19455step1Labels := by
      have hz : ∀ j, raw19455step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19455step1 = (fun i j => raw19455step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19455step1 raw19455step0; decide +kernel
      have hl : raw19455step1Labels = raw19455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19455step0 raw19455step0Labels permutation56 hz
    mixedMoment B raw19455step1 raw19455step1Labels = mixedMoment B raw19455step2 raw19455step2Labels := by
      have ha : raw19455step2 = (fun i j => raw19455step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19455step2 raw19455step1; decide +kernel
      have hl : raw19455step2Labels = raw19455step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19455step1 raw19455step1Labels permutation31 permutation2
    mixedMoment B raw19455step2 raw19455step2Labels = mixedMoment B raw19455step3 raw19455step3Labels := by
      have ha : raw19455step3 = -raw19455step2 := by apply Matrix.ext; change ∀ i j, raw19455step3 i j = -(raw19455step2 i j); unfold raw19455step3 raw19455step2; decide +kernel
      have hl : raw19455step3Labels = raw19455step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node828 node828Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
